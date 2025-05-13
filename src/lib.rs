//! # Rusty Region
//!
//! A parser for DS9 region files, written in Rust using nom 7.1.
//! This library provides tools to parse region file strings into structured data.
//! Includes Python bindings via PyO3.

// --- PyO3 Imports ---
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;
use pyo3::types::PyTuple; // For returning tuples to Python

// --- Nom Imports ---
use nom::{
    IResult,
    branch::alt, // For trying different parsers
    character::complete::{alphanumeric1, multispace0, multispace1, char as nom_char},
    bytes::complete::take_while1,
    combinator::{map, map_res, opt, value}, 
    sequence::{preceded, terminated, separated_pair, tuple, pair}, 
    number::complete::double,
    error::{VerboseError, context, ParseError as NomParseErrorTrait, ContextError},
    Finish,
    Parser,
};
use std::collections::HashMap; // For storing shape definitions

// --- Module Declaration ---
mod semantic_parsers; // Declare the new module
use semantic_parsers::*; // Bring functions into scope


// --- Custom Error Type for Nom ---
type NomVerboseError<'a> = VerboseError<&'a str>;

// --- Semantic Type Definitions ---

/// Describes the semantic meaning of a coordinate parameter for a shape.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum SemanticCoordType {
    CoordOdd,   // e.g., RA, X
    CoordEven,  // e.g., Dec, Y
    Distance,   // e.g., radius, width, height
    Angle,      // e.g., rotation angle, start/end angle for pie
    Integer,    // e.g., number of annulus sectors (parsed as f64 for now)
}

/// Defines the expected coordinate signature for a shape.
#[derive(Debug, Clone)]
pub struct ShapeSignature {
    pub name: &'static str, // For error messages
    /// Parameters that appear before any repeating block.
    pub fixed_head: &'static [SemanticCoordType],
    /// The sequence of types that forms a single repeating unit.
    pub repeat_unit: Option<&'static [SemanticCoordType]>,
    /// Minimum number of times the `repeat_unit` must appear.
    /// If `repeat_unit` is None, this should typically be 0.
    pub min_repeats: usize,
    /// Maximum number of times the `repeat_unit` can appear.
    /// `None` means unbounded. If `repeat_unit` is None, this is irrelevant.
    pub max_repeats: Option<usize>,
    /// Parameters that appear after all repeating blocks.
    pub fixed_tail: &'static [SemanticCoordType],
}

// --- Data Structures ---

/// Represents the coordinate system.
#[derive(Debug, PartialEq, Clone)]
pub enum CoordSystem {
    Physical, Image, Fk4, B1950, Fk5, J2000, Galactic, Ecliptic, Icrs,
    Linear, Amplifier, Detector,
    Unknown(String),
}

impl CoordSystem {
    fn from_str(s: &str) -> Self {
        match s.to_uppercase().as_str() {
            "PHYSICAL" => CoordSystem::Physical,
            "IMAGE" => CoordSystem::Image,
            "FK4" => CoordSystem::Fk4,
            "B1950" => CoordSystem::B1950,
            "FK5" => CoordSystem::Fk5,
            "J2000" => CoordSystem::J2000,
            "GALACTIC" => CoordSystem::Galactic,
            "ECLIPTIC" => CoordSystem::Ecliptic,
            "ICRS" => CoordSystem::Icrs,
            "LINEAR" => CoordSystem::Linear,
            "AMPLIFIER" => CoordSystem::Amplifier,
            "DETECTOR" => CoordSystem::Detector,
            _ => CoordSystem::Unknown(s.to_string()),
        }
    }

    fn to_string_py(&self) -> String {
        match self {
            CoordSystem::Physical => "PHYSICAL", CoordSystem::Image => "IMAGE",
            CoordSystem::Fk4 => "FK4", CoordSystem::B1950 => "B1950",
            CoordSystem::Fk5 => "FK5", CoordSystem::J2000 => "J2000",
            CoordSystem::Galactic => "GALACTIC", CoordSystem::Ecliptic => "ECLIPTIC",
            CoordSystem::Icrs => "ICRS", CoordSystem::Linear => "LINEAR",
            CoordSystem::Amplifier => "AMPLIFIER", CoordSystem::Detector => "DETECTOR",
            CoordSystem::Unknown(s) => return s.clone(),
        }.to_string()
    }
}


/// Represents the type of a geometric shape. (Rust internal)
#[derive(Debug, PartialEq, Clone)]
pub enum ShapeType {
    Circle, Ellipse, Box, RotBox, Polygon, Point, Line, Annulus, Pie,
    Panda, Epanda, Bpanda, Vector, Text,
    Unsupported(String),
}

impl ShapeType {
    fn to_string_py(&self) -> String {
        match self {
            ShapeType::Circle => "circle", ShapeType::Ellipse => "ellipse", ShapeType::Box => "box",
            ShapeType::RotBox => "rotbox", ShapeType::Polygon => "polygon", ShapeType::Point => "point",
            ShapeType::Line => "line", ShapeType::Annulus => "annulus", ShapeType::Pie => "pie",
            ShapeType::Panda => "panda", ShapeType::Epanda => "epanda", ShapeType::Bpanda => "bpanda",
            ShapeType::Vector => "vector", ShapeType::Text => "text",
            ShapeType::Unsupported(s) => return format!("unsupported({})", s),
        }.to_string()
    }
}

/// Represents a key-value property. (Exposed to Python)
#[pyclass(get_all, set_all)]
#[derive(Debug, PartialEq, Clone)]
pub struct Property {
    pub key: String,
    pub value: String,
}

#[pymethods]
impl Property {
    #[new]
    fn new(key: String, value: String) -> Self { Property { key, value } }
}

/// Represents a parsed shape. (Exposed to Python)
#[pyclass]
#[derive(Debug, Clone)]
pub struct Shape {
    #[pyo3(get)]
    shape_type_str: String,
    #[pyo3(get)]
    coordinates: Vec<f64>, // Still Vec<f64> for now
    #[pyo3(get)]
    properties: Vec<Py<Property>>, // Python objects
}

#[pymethods]
impl Shape {
    #[new]
    fn new(shape_type_str: String, coordinates: Vec<f64>, properties: Vec<Py<Property>>) -> Self {
        Shape { shape_type_str, coordinates, properties }
    }
}

// --- Parser Implementation ---

type Input<'a> = &'a str;
type ParserResult<'a, O> = IResult<Input<'a>, O, NomVerboseError<'a>>;

// --- Basic Parsers ---
pub(crate) fn ws<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { multispace0(input) }
fn ws1<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { multispace1(input) }

pub(crate) fn parse_f64_raw<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    double(input)
}

fn parse_identifier_str<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    context("identifier", preceded(ws, terminated(alphanumeric1, ws)))(input)
}

// --- Coordinate System Parser ---
fn parse_coord_system_command<'a>(input: Input<'a>) -> ParserResult<'a, CoordSystem> {
    context(
        "coordinate system command",
        map(
            alphanumeric1,
            |s: &str| CoordSystem::from_str(s)
        )
    )(input)
}


// --- Component Parsers (for shapes) ---
fn comma_sep<'a>(input: Input<'a>) -> ParserResult<'a, ()> {
    value((), tuple((ws, nom_char(','), ws)))(input)
}

fn parse_semantic_sequence<'a>(
    param_types: &'static [SemanticCoordType],
) -> impl FnMut(Input<'a>) -> ParserResult<'a, Vec<f64>> {
    move |mut i: Input| {
        let mut coords = Vec::with_capacity(param_types.len());
        if param_types.is_empty() { return Ok((i, coords)); }
        let (next_i, val) = dispatch_semantic_parser(param_types[0])(i)?;
        coords.push(val);
        i = next_i;
        for &semantic_type in param_types.iter().skip(1) {
            let (next_i_comma, _) = comma_sep(i)?;
            let (next_i_val, val) = dispatch_semantic_parser(semantic_type)(next_i_comma)?;
            coords.push(val);
            i = next_i_val;
        }
        Ok((i, coords))
    }
}

fn parse_coordinates_by_signature<'a>(
    signature: &'static ShapeSignature,
) -> impl FnMut(Input<'a>) -> ParserResult<'a, Vec<f64>> {
    move |mut i: Input| {
        let mut all_coords = Vec::new();
        let original_input_for_error_reporting = i; 
        if !signature.fixed_head.is_empty() {
            let (next_i, head_coords) = parse_semantic_sequence(signature.fixed_head)(i)?;
            all_coords.extend(head_coords);
            i = next_i;
        }
        let mut actual_repeats = 0;
        if let Some(repeat_unit_def) = signature.repeat_unit {
            if !repeat_unit_def.is_empty() {
                for _ in 0..signature.min_repeats {
                    if !all_coords.is_empty() { let (next_i, _) = comma_sep(i)?; i = next_i; }
                    let (next_i, unit_coords) = parse_semantic_sequence(repeat_unit_def)(i)?;
                    all_coords.extend(unit_coords); i = next_i; actual_repeats += 1;
                }
                let max_additional_repeats = signature.max_repeats.map_or(usize::MAX, |max_r| if max_r >= signature.min_repeats { max_r - signature.min_repeats } else { 0 });
                for _ in 0..max_additional_repeats {
                    let mut temp_i = i;
                    if !all_coords.is_empty() { match comma_sep(temp_i) { Ok((next_i, _)) => temp_i = next_i, Err(_) => break, } }
                    match parse_semantic_sequence(repeat_unit_def)(temp_i) {
                        Ok((next_i, unit_coords)) => { all_coords.extend(unit_coords); i = next_i; actual_repeats += 1; }
                        Err(_) => break, 
                    }
                }
            }
        }
        if signature.repeat_unit.is_some() {
            if actual_repeats < signature.min_repeats { return Err(nom::Err::Error(NomVerboseError::add_context(original_input_for_error_reporting, "not enough repeat units", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(original_input_for_error_reporting, nom::error::ErrorKind::ManyMN)))); }
            if let Some(max_r) = signature.max_repeats { if actual_repeats > max_r { return Err(nom::Err::Error(NomVerboseError::add_context(original_input_for_error_reporting, "too many repeat units", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(original_input_for_error_reporting, nom::error::ErrorKind::ManyMN)))); } }
        }
        if !signature.fixed_tail.is_empty() {
            if !all_coords.is_empty() { let (next_i, _) = comma_sep(i)?; i = next_i; }
            let (next_i, tail_coords) = parse_semantic_sequence(signature.fixed_tail)(i)?;
            all_coords.extend(tail_coords); i = next_i;
        }
        if all_coords.is_empty() && signature.fixed_head.is_empty() && signature.fixed_tail.is_empty() && signature.min_repeats == 0 {} 
        else if all_coords.is_empty() && ( !signature.fixed_head.is_empty() || !signature.fixed_tail.is_empty() || signature.min_repeats > 0) {
            return Err(nom::Err::Error(NomVerboseError::add_context(original_input_for_error_reporting, "expected coordinates but found none", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(original_input_for_error_reporting, nom::error::ErrorKind::Eof))));
        }
        Ok((i, all_coords))
    }
}

fn parse_property_value_str<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    context("property value", take_while1(|c: char| !c.is_whitespace() && c != '#'))(input)
}

fn parse_property_internal<'a>(input: Input<'a>) -> ParserResult<'a, Property> {
    context("property", map(separated_pair(parse_identifier_str, tuple((ws, nom_char('='), ws)), parse_property_value_str), |(k, v)| Property { key: k.to_string(), value: v.to_string() } ))(input)
}

fn parse_optional_properties_internal<'a>(input: Input<'a>) -> ParserResult<'a, Vec<Property>> {
    context("optional properties", map(opt(preceded(context("property marker '#'", tuple((ws, nom_char('#'), ws1))), nom::multi::separated_list0(ws1, parse_property_internal))), |opt_props| opt_props.unwrap_or_else(Vec::new)))(input)
}

// --- Shape Definition Logic ---
macro_rules! sct_slice { ($($x:expr),* $(,)?) => { &[$($x),*] } }
use SemanticCoordType::*;
static CIRCLE_SIG: ShapeSignature = ShapeSignature { name: "circle", fixed_head: sct_slice![CoordOdd, CoordEven, Distance], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static ELLIPSE_SIG: ShapeSignature = ShapeSignature { name: "ellipse", fixed_head: sct_slice![CoordOdd, CoordEven, Distance, Distance, Angle], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static BOX_SIG: ShapeSignature = ShapeSignature { name: "box", fixed_head: sct_slice![CoordOdd, CoordEven], repeat_unit: Some(sct_slice![Distance, Distance]), min_repeats: 1, max_repeats: Some(1), fixed_tail: sct_slice![Angle] };
static ROTBOX_SIG: ShapeSignature = ShapeSignature { name: "rotbox", fixed_head: sct_slice![CoordOdd, CoordEven], repeat_unit: Some(sct_slice![Distance, Distance]), min_repeats: 1, max_repeats: Some(1), fixed_tail: sct_slice![Angle] };
static POLYGON_SIG: ShapeSignature = ShapeSignature { name: "polygon", fixed_head: sct_slice![], repeat_unit: Some(sct_slice![CoordOdd, CoordEven]), min_repeats: 3, max_repeats: None, fixed_tail: sct_slice![] };
static POINT_SIG: ShapeSignature = ShapeSignature { name: "point", fixed_head: sct_slice![CoordOdd, CoordEven], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static LINE_SIG: ShapeSignature = ShapeSignature { name: "line", fixed_head: sct_slice![CoordOdd, CoordEven, CoordOdd, CoordEven], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static ANNULUS_SIG: ShapeSignature = ShapeSignature { name: "annulus", fixed_head: sct_slice![CoordOdd, CoordEven], repeat_unit: Some(sct_slice![Distance]), min_repeats: 1, max_repeats: None, fixed_tail: sct_slice![] };
static PIE_SIG: ShapeSignature = ShapeSignature { name: "pie", fixed_head: sct_slice![CoordOdd, CoordEven, Distance, Distance, Angle, Angle], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static VECTOR_SIG: ShapeSignature = ShapeSignature { name: "vector", fixed_head: sct_slice![CoordOdd, CoordEven, Distance, Angle], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static TEXT_SIG: ShapeSignature = ShapeSignature { name: "text", fixed_head: sct_slice![CoordOdd, CoordEven], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![] };
static PANDA_SIG: ShapeSignature = ShapeSignature { name: "panda", fixed_head: sct_slice![CoordOdd, CoordEven, Angle, Angle, Integer, Distance, Distance, Integer], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![]};
static EPANDA_SIG: ShapeSignature = ShapeSignature { name: "epanda", fixed_head: sct_slice![CoordOdd, CoordEven, Angle, Angle, Integer, Distance, Distance, Distance, Distance, Integer, Angle], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![]};
static BPANDA_SIG: ShapeSignature = ShapeSignature { name: "bpanda", fixed_head: sct_slice![CoordOdd, CoordEven, Angle, Angle, Integer, Distance, Distance, Distance, Distance, Integer, Angle], repeat_unit: None, min_repeats: 0, max_repeats: None, fixed_tail: sct_slice![]};

fn get_shape_signature(shape_name_lc: &str) -> Option<&'static ShapeSignature> {
    match shape_name_lc {
        "circle" => Some(&CIRCLE_SIG), "ellipse" => Some(&ELLIPSE_SIG),
        "box" => Some(&BOX_SIG), "rotbox" => Some(&ROTBOX_SIG),
        "polygon" => Some(&POLYGON_SIG), "point" => Some(&POINT_SIG),
        "line" => Some(&LINE_SIG), "annulus" => Some(&ANNULUS_SIG),
        "pie" => Some(&PIE_SIG), "vector" => Some(&VECTOR_SIG),
        "text" => Some(&TEXT_SIG), "panda" => Some(&PANDA_SIG),
        "epanda" => Some(&EPANDA_SIG), "bpanda" => Some(&BPANDA_SIG),
        _ => None,
    }
}

// --- Shape Parser (Rust internal result) ---
// This function parses the shape part: `shape_keyword(coords) # properties`
fn parse_shape_and_props<'a>(input: Input<'a>) -> ParserResult<'a, (ShapeType, Vec<f64>, Vec<Property>)> {
    let (i, shape_keyword) = parse_identifier_str(input)?;
    let shape_keyword_lc = shape_keyword.to_lowercase();
    let shape_type_enum = match shape_keyword_lc.as_str() {
        "circle" => ShapeType::Circle, "ellipse" => ShapeType::Ellipse,
        "box" => ShapeType::Box, "rotbox" => ShapeType::RotBox,
        "polygon" => ShapeType::Polygon, "point" => ShapeType::Point,
        "line" => ShapeType::Line, "annulus" => ShapeType::Annulus,
        "pie" => ShapeType::Pie, "panda" => ShapeType::Panda,
        "epanda" => ShapeType::Epanda, "bpanda" => ShapeType::Bpanda,
        "vector" => ShapeType::Vector, "text" => ShapeType::Text,
        _ => ShapeType::Unsupported(shape_keyword.to_string()),
    };

    let (i, coords) = if let ShapeType::Unsupported(_) = shape_type_enum {
        preceded(
            context("opening parenthesis for unsupported shape", tuple((ws, nom_char('(')))),
            terminated(
                nom::multi::separated_list1(
                    context("coordinate separator comma", tuple((ws, nom_char(','), ws))),
                    context("f64 for unsupported", preceded(ws, terminated(double, ws)))
                ),
                context("closing parenthesis for unsupported shape", tuple((ws, nom_char(')'))))
            )
        )(i)?
    } else if let Some(signature) = get_shape_signature(&shape_keyword_lc) {
        preceded(
            context("opening parenthesis", tuple((ws, nom_char('(')))),
            terminated(
                parse_coordinates_by_signature(signature),
                context("closing parenthesis", tuple((ws, nom_char(')'))))
            )
        )(i)?
    } else {
        return Err(nom::Err::Error(NomVerboseError::add_context(input, "internal signature missing for known shape", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(input, nom::error::ErrorKind::Verify))));
    };

    let (i, props) = parse_optional_properties_internal(i)?;
    Ok((i, (shape_type_enum, coords, props)))
}


// --- Main Line Parsing Logic (Internal Rust) ---
// This function will be the core logic that `parse_single_region_line_for_rust` uses.
// It returns an IResult to be composable.
fn parse_line_content<'a>(input: Input<'a>) -> ParserResult<'a, (Option<CoordSystem>, Option<(ShapeType, Vec<f64>, Vec<Property>)>)> {
    alt((
        // Case 1: COORD_SYSTEM ; SHAPE_DEFINITION
        map(
            tuple((
                parse_coord_system_command,
                ws,
                nom_char(';'),
                ws,
                parse_shape_and_props // Parses shape_keyword(coords) # props
            )),
            |(cs, _, _, _, shape_data)| (Some(cs), Some(shape_data))
        ),
        // Case 2: COORD_SYSTEM (alone on a line)
        map(
            parse_coord_system_command,
            |cs| (Some(cs), None)
        ),
        // Case 3: SHAPE_DEFINITION (alone on a line)
        map(
            parse_shape_and_props, // Parses shape_keyword(coords) # props
            |shape_data| (None, Some(shape_data))
        ),
    ))(input)
}


// --- Main Parsing Function (for Rust usage, returns Result) ---
pub fn parse_single_region_line_for_rust(line: &str) -> Result<(Option<CoordSystem>, Option<(ShapeType, Vec<f64>, Vec<Property>)>), String> {
    match terminated(preceded(ws, parse_line_content), ws)(line).finish() {
        Ok((_remaining, output)) => Ok(output),
        Err(e) => Err(nom::error::convert_error(line, e)),
    }
}

// --- Python Function ---
#[pyfunction]
fn parse_region_line(py: Python<'_>, line: &str) -> PyResult<PyObject> { // Return PyObject for tuple
    match parse_single_region_line_for_rust(line) {
        Ok((coord_system_opt, shape_data_opt)) => {
            let py_coord_system = coord_system_opt.map(|cs| cs.to_string_py()).into_py(py);

            let py_shape = match shape_data_opt {
                Some((shape_type_rust, coords_rust, props_rust)) => {
                    let props_py: Vec<Py<Property>> = props_rust
                        .into_iter()
                        .map(|p_rust| Py::new(py, p_rust))
                        .collect::<PyResult<_>>()?;

                    let shape_obj = Shape::new(
                        shape_type_rust.to_string_py(),
                        coords_rust,
                        props_py,
                    );
                    Some(Py::new(py, shape_obj)?)
                }
                None => None,
            };
            
            // Create a Python tuple using an array/slice
            let tuple_elements: [PyObject; 2] = [py_coord_system, py_shape.into_py(py)];
            Ok(PyTuple::new_bound(py, &tuple_elements).into_py(py))
        }
        Err(e_str) => Err(PyValueError::new_err(e_str)),
    }
}

// --- Python Module Definition ---
#[pymodule]
fn rusty_region_parser(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(parse_region_line, m)?)?;
    m.add_class::<Shape>()?;
    m.add_class::<Property>()?;
    Ok(())
}

// --- Unit Tests (Rust tests) ---
#[cfg(test)]
mod tests {
    use super::*;

     macro_rules! assert_rust_parses_line {
        ($input:expr, $expected_cs:expr, $expected_shape_type:pat, $expected_coords_len:expr, $expected_props_len:expr) => {
            match parse_single_region_line_for_rust($input) {
                Ok((cs_opt, shape_data_opt)) => {
                    assert_eq!(cs_opt, $expected_cs, "CoordSystem mismatch for '{}'", $input);
                    match shape_data_opt {
                        Some((shape_type, coords, props)) => {
                            assert!(matches!(shape_type, $expected_shape_type), "Shape type mismatch for '{}'. Got: {:?}", $input, shape_type);
                            assert_eq!(coords.len(), $expected_coords_len, "Coordinate count mismatch for '{}'. Got: {:?}, expected {}", $input, coords, $expected_coords_len);
                            assert_eq!(props.len(), $expected_props_len, "Property count mismatch for '{}'. Got: {:?}, expected {}", $input, props, $expected_props_len);
                        },
                        None => {
                            // This case should only be hit if $expected_shape_type is None (which we can't pat match directly here)
                            // For simplicity, if $expected_coords_len is 0 and $expected_props_len is 0 and $expected_shape_type is a wildcard, assume it's fine.
                            // A more robust macro would handle Option<ShapeTypePattern>.
                             if $expected_coords_len != 0 || $expected_props_len != 0 {
                                panic!("Expected shape data but got None for '{}'", $input);
                            }
                        }
                    }
                },
                Err(e_str) => panic!("Internal parsing failed for '{}':\n{}", $input, e_str),
            }
        };
        ($input:expr, $expected_cs:expr, None) => { // For lines with only coord system
             match parse_single_region_line_for_rust($input) {
                Ok((cs_opt, shape_data_opt)) => {
                    assert_eq!(cs_opt, $expected_cs, "CoordSystem mismatch for '{}'", $input);
                    assert!(shape_data_opt.is_none(), "Expected no shape data but got Some for '{}'", $input);
                },
                Err(e_str) => panic!("Internal parsing failed for '{}':\n{}", $input, e_str),
            }
        };
    }


     macro_rules! assert_rust_fails {
        ($input:expr) => {
            let result = parse_single_region_line_for_rust($input);
             if result.is_ok() {
                 panic!("Internal parsing should have failed for '{}' but succeeded with: {:?}", $input, result.unwrap());
             }
             assert!(result.is_err());
        };
    }

    #[test]
    fn test_rust_parse_coord_system_only() {
        assert_rust_parses_line!("fk5", Some(CoordSystem::Fk5), None);
        assert_rust_parses_line!(" IMAGE ", Some(CoordSystem::Image), None);
        assert_rust_parses_line!("physical", Some(CoordSystem::Physical), None);
    }

    #[test]
    fn test_rust_parse_coord_system_with_shape() {
        assert_rust_parses_line!("fk5; circle(1,2,3)", Some(CoordSystem::Fk5), ShapeType::Circle, 3, 0);
        assert_rust_parses_line!(" J2000 ; point(10,20) # text={test}", Some(CoordSystem::J2000), ShapeType::Point, 2, 1);
    }
    
    #[test]
    fn test_rust_parse_shape_only_no_coord_system() {
         assert_rust_parses_line!("circle(100, 200, 30)", None, ShapeType::Circle, 3, 0);
    }


    #[test]
    fn test_rust_parse_simple_circle() {
        let line = "circle(100, 200, 30)";
        assert_rust_parses_line!(line, None, ShapeType::Circle, 3, 0);
    }

    #[test]
    fn test_rust_parse_polygon_valid() {
        let line = "polygon(1,2,3,4,5,6)"; // 3 pairs
        assert_rust_parses_line!(line, None, ShapeType::Polygon, 6, 0);
        let line2 = "polygon(1,2,3,4,5,6,7,8)"; // 4 pairs
        assert_rust_parses_line!(line2, None, ShapeType::Polygon, 8, 0);
    }

    #[test]
    fn test_rust_parse_polygon_invalid_count() {
        let line_too_few = "polygon(1,2,3,4)"; // 2 pairs, less than min 3 pairs (6 coords)
        assert_rust_fails!(line_too_few);

        let line_misaligned = "polygon(1,2,3,4,5,6,7)"; // 7 coords, not pairs
        assert_rust_fails!(line_misaligned);
    }

    #[test]
    fn test_rust_parse_box_valid() {
        let line = "box(1,2,10,20,0)";
        assert_rust_parses_line!(line, None, ShapeType::Box, 5,0);
    }
     #[test]
    fn test_rust_parse_rotbox_valid() {
        let line = "rotbox(1,2,10,20,30)";
        assert_rust_parses_line!(line, None, ShapeType::RotBox, 5,0);
    }


    #[test]
    fn test_rust_parse_annulus_valid() {
        let line_3_params = "annulus(1,2,10)"; // x,y,r_inner
        assert_rust_parses_line!(line_3_params, None, ShapeType::Annulus, 3, 0);
        let line_4_params = "annulus(1,2,10,20)"; // x,y,r_inner, r_outer1
        assert_rust_parses_line!(line_4_params, None, ShapeType::Annulus, 4, 0);
        let line_5_params = "annulus(1,2,10,20,30)"; // x,y,r_inner, r_outer1, r_outer2
        assert_rust_parses_line!(line_5_params, None, ShapeType::Annulus, 5, 0);
    }

    #[test]
    fn test_rust_parse_annulus_invalid() {
        let line_too_few = "annulus(1,2)"; // Needs at least x,y,r_inner
        assert_rust_fails!(line_too_few);
    }


    #[test]
    fn test_rust_parse_circle_with_whitespace() {
        let line = "  circle  ( 100.5 ,  200 , 30 )   ";
        assert_rust_parses_line!(line, None, ShapeType::Circle, 3, 0);
    }

    #[test]
    fn test_rust_parse_circle_with_properties() {
        let line = "circle( 10.5, 20 , 5.0 ) # color=red width=2 tag=foo";
        assert_rust_parses_line!(line, None, ShapeType::Circle, 3, 3);
         match parse_single_region_line_for_rust(line) {
             Ok((_, Some((_, _, props)))) => {
                 assert_eq!(props[0], Property { key: "color".to_string(), value: "red".to_string() });
                 assert_eq!(props[1], Property { key: "width".to_string(), value: "2".to_string() });
                 assert_eq!(props[2], Property { key: "tag".to_string(), value: "foo".to_string() });
             },
             _ => panic!("Should have parsed successfully with shape data"),
         }
    }

    #[test]
    fn test_rust_parse_ellipse() {
        let line = "ellipse(500, 500, 20.1, 10.9, 45)";
        assert_rust_parses_line!(line, None, ShapeType::Ellipse, 5, 0);
    }

    #[test]
    fn test_rust_invalid_syntax_missing_coord() {
        let line = "circle(100, 200, )";
        assert_rust_fails!(line);
    }

    #[test]
    fn test_rust_invalid_syntax_unclosed_paren() {
        let line = "circle(100, 200, 30";
        assert_rust_fails!(line);
    }

    #[test]
    fn test_rust_unsupported_shape_name() {
        let line = "someunknownshape(1, 2, 10, 0) # property=value";
        // This will be parsed as ShapeType::Unsupported
        assert_rust_parses_line!(line, None, ShapeType::Unsupported(_), 4, 1);
         match parse_single_region_line_for_rust(line) {
             Ok((_, Some((shape_type, _, props)))) => {
                 match shape_type {
                     ShapeType::Unsupported(s) => assert!(s.eq_ignore_ascii_case("someunknownshape")),
                     _ => panic!("Expected Unsupported shape type"),
                 }
                 assert_eq!(props[0], Property { key: "property".to_string(), value: "value".to_string() });
             },
             _ => panic!("Should have parsed successfully with shape data"),
         }
    }
     #[test]
    fn test_rust_vector_shape_defined() {
        let line = "vector(1,2,3,4)";
        assert_rust_parses_line!(line, None, ShapeType::Vector, 4,0);
    }


}
