//! # Rusty Region
//!
//! A parser for DS9 region files, written in Rust using nom 7.1.
//! This library provides tools to parse region file strings into structured data.
//! Includes Python bindings via PyO3.

// --- PyO3 Imports ---
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;
use pyo3::types::{PyTuple, PyDict, PyList};

// --- Nom Imports ---
use nom::{
    IResult,
    branch::alt, 
    character::complete::{alphanumeric1, multispace0, multispace1, char as nom_char, digit1, not_line_ending, line_ending},
    bytes::complete::{take_while1, tag_no_case, take_until}, 
    combinator::{map, map_res, opt, value, recognize, cut, eof, peek}, 
    sequence::{preceded, terminated, separated_pair, tuple, pair, delimited}, 
    multi::{separated_list0, separated_list1, many0_count},
    number::complete::double,
    error::{VerboseError, context, ParseError as NomParseErrorTrait, ContextError},
    Finish,
    Parser,
};
use std::collections::HashMap; 

// --- Module Declaration ---
mod semantic_parsers; 
use semantic_parsers::*; 


// --- Custom Error Type for Nom ---
type NomVerboseError<'a> = VerboseError<&'a str>;

// --- Semantic Type Definitions ---
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum SemanticCoordType { CoordOdd, CoordEven, Distance, Angle, Integer }

#[derive(Debug, Clone)]
pub struct ShapeSignature {
    pub name: &'static str, 
    pub fixed_head: &'static [SemanticCoordType],
    pub repeat_unit: Option<&'static [SemanticCoordType]>,
    pub min_repeats: usize,
    pub max_repeats: Option<usize>,
    pub fixed_tail: &'static [SemanticCoordType],
}

// --- Attribute Value Definition (used for both Global and Shape Properties) ---
#[derive(Debug, PartialEq, Clone)]
pub enum AttributeValue {
    String(String),
    Number(f64),
    NumberList(Vec<f64>),
    Flag(bool), 
}

// --- Data Structures ---
#[derive(Debug, PartialEq, Clone)]
pub enum CoordSystem {
    Physical, Image, Fk4, B1950, Fk5, J2000, Galactic, Ecliptic, Icrs,
    Linear, Amplifier, Detector,
    Unknown(String), 
}
impl CoordSystem { 
    fn from_str(s: &str) -> Self {
        match s.to_uppercase().as_str() {
            "PHYSICAL" => CoordSystem::Physical, "IMAGE" => CoordSystem::Image,
            "FK4" => CoordSystem::Fk4, "B1950" => CoordSystem::B1950,
            "FK5" => CoordSystem::Fk5, "J2000" => CoordSystem::J2000,
            "GALACTIC" => CoordSystem::Galactic, "ECLIPTIC" => CoordSystem::Ecliptic,
            "ICRS" => CoordSystem::Icrs, "LINEAR" => CoordSystem::Linear,
            "AMPLIFIER" => CoordSystem::Amplifier, "DETECTOR" => CoordSystem::Detector,
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
#[derive(Debug, PartialEq, Clone)]
pub enum ShapeType { 
    Circle, Ellipse, Box, RotBox, Polygon, Point, Line, Annulus, Pie,
    Panda, Epanda, Bpanda, Vector, Text, Ruler, 
    Unsupported(String),
}
impl ShapeType { 
    fn to_string_py(&self) -> String {
        match self {
            ShapeType::Circle => "circle", ShapeType::Ellipse => "ellipse", ShapeType::Box => "box",
            ShapeType::RotBox => "rotbox", ShapeType::Polygon => "polygon", ShapeType::Point => "point",
            ShapeType::Line => "line", ShapeType::Annulus => "annulus", ShapeType::Pie => "pie",
            ShapeType::Panda => "panda", ShapeType::Epanda => "epanda", ShapeType::Bpanda => "bpanda",
            ShapeType::Vector => "vector", ShapeType::Text => "text", ShapeType::Ruler => "ruler",
            ShapeType::Unsupported(s) => return format!("unsupported({})", s),
        }.to_string()
    }
}

#[pyclass(get_all, set_all)] 
#[derive(Debug, PartialEq, Clone)] 
pub struct Property { 
    pub key: String,
    pub value: String, 
}

#[pymethods]
impl Property {
    #[new]
    fn new(key: String, value: String) -> Self {
        Property { key, value }
    }
}

#[pyclass]
#[derive(Debug, Clone)]
pub struct Shape {
    pub shape_type_str: String,
    pub coordinates: Vec<f64>, 
    pub coordinate_formats: Vec<u8>, // Store format as integers for Python exposure
    pub properties_internal: HashMap<String, AttributeValue>,
    pub tags_internal: Vec<String>, 
    pub exclude: bool,
}

#[pymethods] 
impl Shape { 
    // Getter methods for fields
    fn get_shape_type_str(&self) -> String {
        self.shape_type_str.clone()
    }
    
    fn get_coordinates(&self) -> Vec<f64> {
        self.coordinates.clone()
    }
    
    fn get_coordinate_formats(&self) -> Vec<u8> {
        self.coordinate_formats.clone()
    }
    
    fn get_exclude(&self) -> bool {
        self.exclude
    }
    
    #[new]
    #[pyo3(signature = (shape_type_str, coordinates, coordinate_formats=None, properties_py=None, tags_internal=vec![], exclude=false))]
    fn new(
        shape_type_str: String, 
        coordinates: Vec<f64>, 
        coordinate_formats: Option<Vec<u8>>, // Accept integers for Python compatibility
        properties_py: Option<&Bound<'_, PyDict>>, 
        tags_internal: Vec<String>, 
        exclude: bool
    ) -> PyResult<Self> { 
        let mut properties_internal_map = HashMap::new();
        if let Some(props) = properties_py {
            for (key_obj, value_obj) in props.iter() {
            let key: String = key_obj.extract()?;
            let attr_value = if let Ok(s) = value_obj.extract::<String>() {
                AttributeValue::String(s)
            } else if let Ok(f) = value_obj.extract::<f64>() {
                AttributeValue::Number(f)
            } else if let Ok(b) = value_obj.extract::<bool>() {
                AttributeValue::Flag(b)
            } else if let Ok(list_f64) = value_obj.extract::<Vec<f64>>() {
                 AttributeValue::NumberList(list_f64)
            } else if let Ok(list_i64) = value_obj.extract::<Vec<i64>>() { 
                 AttributeValue::NumberList(list_i64.into_iter().map(|x| x as f64).collect())
            }
            else {
                return Err(PyValueError::new_err(format!("Unsupported value type for property '{}'", key)));
            };
            properties_internal_map.insert(key, attr_value);
            }
        }

        Ok(Shape {
            shape_type_str,
            coordinates,
            coordinate_formats: coordinate_formats.unwrap_or_default(),
            properties_internal: properties_internal_map,
            tags_internal,
            exclude,
        }) 
    }

    fn properties(&self, py: Python<'_>) -> PyResult<Py<PyDict>> {
        let dict = PyDict::new_bound(py);
        for (k, v_enum) in &self.properties_internal {
            let py_val = match v_enum {
                AttributeValue::String(s) => s.to_object(py),
                AttributeValue::Number(n) => n.to_object(py),
                AttributeValue::NumberList(nl) => nl.to_object(py),
                AttributeValue::Flag(b) => b.to_object(py),
            };
            dict.set_item(k, py_val)?;
        }
        Ok(dict.into())
    }

    fn tags(&self, py: Python<'_>) -> PyResult<Py<PyList>> {
        Ok(PyList::new_bound(py, &self.tags_internal).into())
    }
}

// --- Parser Implementation ---
type Input<'a> = &'a str;
type ParserResult<'a, O> = IResult<Input<'a>, O, NomVerboseError<'a>>;

// --- Basic Parsers ---
pub(crate) fn ws<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { multispace0(input) }
fn ws1<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { multispace1(input) }
pub(crate) fn parse_f64_raw<'a>(input: Input<'a>) -> ParserResult<'a, f64> { double(input) }

fn parse_identifier_str_no_leading_ws<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    context("identifier_no_leading_ws", terminated(alphanumeric1, ws))(input)
}

// --- Coordinate System Parser ---
fn parse_coord_system_command<'a>(input: Input<'a>) -> ParserResult<'a, CoordSystem> { 
    context(
        "coordinate system command",
        alt((
            map(tag_no_case("PHYSICAL"), |_| CoordSystem::Physical), map(tag_no_case("IMAGE"), |_| CoordSystem::Image),
            map(tag_no_case("FK4"), |_| CoordSystem::Fk4), map(tag_no_case("B1950"), |_| CoordSystem::B1950),
            map(tag_no_case("FK5"), |_| CoordSystem::Fk5), map(tag_no_case("J2000"), |_| CoordSystem::J2000),
            map(tag_no_case("GALACTIC"), |_| CoordSystem::Galactic), map(tag_no_case("ECLIPTIC"), |_| CoordSystem::Ecliptic),
            map(tag_no_case("ICRS"), |_| CoordSystem::Icrs), map(tag_no_case("LINEAR"), |_| CoordSystem::Linear),
            map(tag_no_case("AMPLIFIER"), |_| CoordSystem::Amplifier), map(tag_no_case("DETECTOR"), |_| CoordSystem::Detector),
        ))
    )(input)
}

// --- Attribute Parsers ---

fn parse_delimited_string_value<'a>(input: Input<'a>) -> ParserResult<'a, String> { 
    context(
        "delimited string value",
        alt((
            map(delimited(nom_char('"'), take_until("\""), nom_char('"')), |s: &str| s.to_string()),
            map(delimited(nom_char('\''), take_until("'"), nom_char('\'')), |s: &str| s.to_string()),
            map(delimited(nom_char('{'), take_until("}"), nom_char('}')), |s: &str| s.to_string()),
        ))
    )(input)
}
fn parse_dashlist_value<'a>(input: Input<'a>) -> ParserResult<'a, Vec<f64>> { 
    context("dashlist value", nom::multi::separated_list1(ws1, double))(input)
}
fn parse_flag_value<'a>(input: Input<'a>) -> ParserResult<'a, bool> { 
    context("flag value (0 or 1)", alt((map(nom_char('1'), |_| true), map(nom_char('0'), |_| false))))(input)
}
fn parse_simple_word_or_number_value_str<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { 
    recognize(take_while1(|c: char| !c.is_whitespace() && c != '=' && c != '#'))(input)
}

/// Parses a single attribute pair (key=value) or a valueless key.
/// Returns (key_string, AttributeValue) or just (key_string, AttributeValue::Flag(true)) for valueless.
fn parse_attribute_pair<'a>(input: Input<'a>) -> ParserResult<'a, (String, AttributeValue)> { 
    let (i, key_str_val) = parse_identifier_str_no_leading_ws(input)?; 
    let key_lc = key_str_val.trim().to_lowercase();
    
    let (i, opt_value_parser_result) = opt(preceded(tuple((ws, nom_char('='), ws)), 
        alt((
            |i_val: Input<'a>| if key_lc == "dashlist" || key_lc == "line" { map(parse_dashlist_value, AttributeValue::NumberList)(i_val) } else { Err(nom::Err::Error(NomVerboseError::from_error_kind(i_val, nom::error::ErrorKind::Alt))) },
            |i_val: Input<'a>| if key_lc == "font" || key_lc == "text" || key_lc == "label" || key_lc == "tag" || key_lc == "format" || key_lc == "ruler" || key_lc == "point" { map(parse_delimited_string_value, AttributeValue::String)(i_val) } else { Err(nom::Err::Error(NomVerboseError::from_error_kind(i_val, nom::error::ErrorKind::Alt))) },
            |i_val: Input<'a>| if ["color"].contains(&key_lc.as_str()) { map(parse_simple_word_or_number_value_str, |s| AttributeValue::String(s.to_string()))(i_val) } else { Err(nom::Err::Error(NomVerboseError::from_error_kind(i_val, nom::error::ErrorKind::Alt))) },
            |i_val: Input<'a>| if ["width", "lw", "lwidth", "radius", "major", "minor", "angle", "alpha", "size", "textangle"].contains(&key_lc.as_str()) { map(double, AttributeValue::Number)(i_val) } else { Err(nom::Err::Error(NomVerboseError::from_error_kind(i_val, nom::error::ErrorKind::Alt))) },
            |i_val: Input<'a>| if ["select", "highlite", "dash", "fixed", "edit", "move", "rotate", "delete", "include", "source", "background", "fill", "textrotate"].contains(&key_lc.as_str()) { map(parse_flag_value, AttributeValue::Flag)(i_val) } else { Err(nom::Err::Error(NomVerboseError::from_error_kind(i_val, nom::error::ErrorKind::Alt))) },
            map(recognize(double), |s: &str| AttributeValue::Number(s.parse().unwrap_or(0.0))), 
            map(parse_simple_word_or_number_value_str, |s| AttributeValue::String(s.to_string())),
        ))
    ))(i)?;

    if let Some(value_enum) = opt_value_parser_result {
        Ok((i, (key_str_val.trim().to_string(), value_enum)))
    } else {
        if ["source", "background", "include", "dash", "fixed", "edit", "move", "rotate", "delete", "select", "highlite", "fill", "textrotate"].contains(&key_lc.as_str()){ 
             Ok((i, (key_str_val.trim().to_string(), AttributeValue::Flag(true))))
        } else {
            Err(nom::Err::Error(NomVerboseError::add_context(input, "expected value for attribute or known valueless flag", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(key_str_val, nom::error::ErrorKind::Tag))))
        }
    }
}

// Parses a list of attributes (key=value pairs or valueless keys)
// Returns a HashMap for general attributes and a Vec<String> for tags
fn parse_attributes_and_tags_list<'a>(input: Input<'a>) -> ParserResult<'a, (HashMap<String, AttributeValue>, Vec<String>)> { 
    map(
        nom::multi::separated_list0(ws1, parse_attribute_pair), 
        |attrs_vec| {
            let mut attrs_map = HashMap::new();
            let mut tags_vec = Vec::new();
            for (key, value) in attrs_vec {
                if key.eq_ignore_ascii_case("tag") {
                    if let AttributeValue::String(s_val) = value {
                        tags_vec.push(s_val);
                    } 
                } else {
                    attrs_map.insert(key, value);
                }
            }
            (attrs_map, tags_vec)
        }
    )(input)
}


fn parse_global_line<'a>(input: Input<'a>) -> ParserResult<'a, (HashMap<String, AttributeValue>, Vec<String>)> { 
    preceded(pair(tag_no_case("global"), ws1), parse_attributes_and_tags_list)(input)
}

// --- Component Parsers (for shapes) ---
fn comma_sep<'a>(input: Input<'a>) -> ParserResult<'a, ()> { value((), tuple((ws, nom_char(','), ws)))(input)}
fn parse_semantic_sequence<'a>(param_types: &'static [SemanticCoordType], active_system: Option<&'a CoordSystem>) -> impl FnMut(Input<'a>) -> ParserResult<'a, (Vec<f64>, Vec<u8>)> + 'a { 
    move |mut i: Input| {
        let mut coords = Vec::with_capacity(param_types.len());
        let mut formats = Vec::with_capacity(param_types.len());
        if param_types.is_empty() { return Ok((i, (coords, formats))); }
        let (next_i, (val, fmt)) = dispatch_semantic_parser(param_types[0], active_system)(i)?;
        coords.push(val);
        formats.push(fmt.to_int()); // Convert CoordFormat to integer
        i = next_i;
        for &semantic_type in param_types.iter().skip(1) {
            let (next_i_comma, _) = comma_sep(i)?;
            let (next_i_val, (val, fmt)) = dispatch_semantic_parser(semantic_type, active_system)(next_i_comma)?;
            coords.push(val);
            formats.push(fmt.to_int()); // Convert CoordFormat to integer
            i = next_i_val;
        }
        Ok((i, (coords, formats)))
    }
}
fn parse_coordinates_by_signature<'a>(signature: &'static ShapeSignature, active_system: Option<&'a CoordSystem>) -> impl FnMut(Input<'a>) -> ParserResult<'a, (Vec<f64>, Vec<u8>)> + 'a { 
    move |mut i: Input| {
        let mut all_coords = Vec::new();
        let mut all_formats = Vec::new();
        let original_input_for_error_reporting = i; 
        if !signature.fixed_head.is_empty() {
            let (next_i, (head_coords, head_formats)) = parse_semantic_sequence(signature.fixed_head, active_system)(i)?;
            all_coords.extend(head_coords);
            all_formats.extend(head_formats);
            i = next_i;
        }
        let mut actual_repeats = 0;
        if let Some(repeat_unit_def) = signature.repeat_unit {
            if !repeat_unit_def.is_empty() {
                for _ in 0..signature.min_repeats {
                    if !all_coords.is_empty() { let (next_i, _) = comma_sep(i)?; i = next_i; }
                    let (next_i, (unit_coords, unit_formats)) = parse_semantic_sequence(repeat_unit_def, active_system)(i)?;
                    all_coords.extend(unit_coords);
                    all_formats.extend(unit_formats);
                    i = next_i; actual_repeats += 1;
                }
                let max_additional_repeats = signature.max_repeats.map_or(usize::MAX, |max_r| if max_r >= signature.min_repeats { max_r - signature.min_repeats } else { 0 });
                for _ in 0..max_additional_repeats {
                    let mut temp_i = i;
                    if !all_coords.is_empty() { match comma_sep(temp_i) { Ok((next_i, _)) => temp_i = next_i, Err(_) => break, } }
                    match parse_semantic_sequence(repeat_unit_def, active_system)(temp_i) {
                        Ok((next_i, (unit_coords, unit_formats))) => { 
                            all_coords.extend(unit_coords); 
                            all_formats.extend(unit_formats);
                            i = next_i; actual_repeats += 1; 
                        }
                        Err(_) => break, 
                    }
                }
            }
        }
        if signature.repeat_unit.is_some() {
            if actual_repeats < signature.min_repeats { return Err(nom::Err::Failure(<NomVerboseError as ContextError<Input<'a>>>::add_context(original_input_for_error_reporting, "not enough repeat units", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(original_input_for_error_reporting, nom::error::ErrorKind::ManyMN)))); }
            if let Some(max_r) = signature.max_repeats { if actual_repeats > max_r { return Err(nom::Err::Failure(<NomVerboseError as ContextError<Input<'a>>>::add_context(original_input_for_error_reporting, "too many repeat units", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(original_input_for_error_reporting, nom::error::ErrorKind::ManyMN)))); } }
        }
        if !signature.fixed_tail.is_empty() {
            if !all_coords.is_empty() { let (next_i, _) = comma_sep(i)?; i = next_i; }
            let (next_i, (tail_coords, tail_formats)) = parse_semantic_sequence(signature.fixed_tail, active_system)(i)?;
            all_coords.extend(tail_coords);
            all_formats.extend(tail_formats);
            i = next_i;
        }
        if all_coords.is_empty() && signature.fixed_head.is_empty() && signature.fixed_tail.is_empty() && signature.min_repeats == 0 {} 
        else if all_coords.is_empty() && ( !signature.fixed_head.is_empty() || !signature.fixed_tail.is_empty() || signature.min_repeats > 0) {
            return Err(nom::Err::Failure(<NomVerboseError as ContextError<Input<'a>>>::add_context(original_input_for_error_reporting, "expected coordinates but found none", <NomVerboseError as NomParseErrorTrait<Input>>::from_error_kind(original_input_for_error_reporting, nom::error::ErrorKind::Eof))));
        }
        Ok((i, (all_coords, all_formats)))
    }
}

// This function parses the properties part of a shape definition (e.g., # color=red width=1)
fn parse_optional_shape_properties_and_tags<'a>(input: Input<'a>) -> ParserResult<'a, (HashMap<String, AttributeValue>, Vec<String>)> {
    alt((
        // Case 1: Has properties (starts with #)
        preceded(
            tuple((ws, nom_char('#'), ws)),
            parse_attributes_and_tags_list
        ),
        // Case 2: No properties, just return empty collections
        map(ws, |_| (HashMap::new(), Vec::new()))
    ))(input)
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
// This function parses the shape part: `[-]shape_keyword(coords) # properties`
// Returns (is_excluded, ShapeType enum, Vec<f64>, Vec<CoordFormat>, HashMap<String, AttributeValue>, Vec<String> for tags)
fn parse_shape_and_props<'a>(
    input: Input<'a>, 
    active_system: Option<&'a CoordSystem> 
) -> ParserResult<'a, (bool, ShapeType, Vec<f64>, Vec<u8>, HashMap<String, AttributeValue>, Vec<String>)> {
    // Parse exclusion character if present
    let (i, opt_exclusion_char) = opt(nom_char('-'))(input)?;
    let exclude = opt_exclusion_char.is_some();
    
    // Consume any whitespace after the exclusion character
    let (i, _) = ws(i)?;
    
    // Parse the shape keyword (e.g., "circle", "box", etc.)
    let (i, shape_keyword) = parse_identifier_str_no_leading_ws(i)?;
    let shape_keyword_lc = shape_keyword.to_lowercase();
    
    // Determine the shape type from the keyword
    let shape_type = match shape_keyword_lc.as_str() {
        "circle" => ShapeType::Circle,
        "ellipse" => ShapeType::Ellipse,
        "box" => ShapeType::Box,
        "rotbox" => ShapeType::RotBox,
        "polygon" => ShapeType::Polygon,
        "point" => ShapeType::Point,
        "line" => ShapeType::Line,
        "annulus" => ShapeType::Annulus,
        "pie" => ShapeType::Pie,
        "panda" => ShapeType::Panda,
        "epanda" => ShapeType::Epanda,
        "bpanda" => ShapeType::Bpanda,
        "vector" => ShapeType::Vector,
        "text" => ShapeType::Text,
        "ruler" => ShapeType::Ruler,
        _ => ShapeType::Unsupported(shape_keyword.to_string()),
    };
    
    // Parse the coordinates based on the shape type
    let (i, (coords, formats)) = if let ShapeType::Unsupported(_) = shape_type {
        // For unsupported shapes, parse a simple list of coordinates
        let (i, coords) = preceded(
            tuple((ws, nom_char('('))),
            terminated(
                separated_list1(
                    tuple((ws, nom_char(','), ws)),
                    preceded(ws, terminated(double, ws))
                ),
                tuple((ws, nom_char(')')))
            )
        )(i)?;
        
        // Create default formats for unsupported shapes (all Simple)
        let formats = coords.iter().map(|_| 
            semantic_parsers::FORMAT_SIMPLE // Use the integer constant instead of enum
        ).collect::<Vec<u8>>();
        
        (i, (coords, formats))
    } else if let Some(signature) = get_shape_signature(&shape_keyword_lc) {
        // For known shapes, use the signature to parse coordinates
        let (i, result) = preceded(
            tuple((ws, nom_char('('))),
            terminated(
                parse_coordinates_by_signature(signature, active_system),
                tuple((ws, nom_char(')')))
            )
        )(i)?;
        
        // Validate the number of coordinates
        let (coords, formats) = result;
        let n_coords = coords.len();
        let min_required = signature.fixed_head.len() + signature.fixed_tail.len();
        
        if n_coords < min_required {
            let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(i, nom::error::ErrorKind::Verify);
            let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(i, "Not enough coordinates for shape", base_err);
            return Err(nom::Err::Failure(ctx_err));
        }
        
        // Validate repeating units if applicable
        if let Some(repeat_unit) = signature.repeat_unit {
            let repeat_unit_len = repeat_unit.len();
            if repeat_unit_len > 0 {
                let remaining_coords = n_coords - min_required;
                if remaining_coords % repeat_unit_len != 0 {
                    let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(i, nom::error::ErrorKind::Verify);
                    let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(i, "Invalid number of coordinates for shape", base_err);
                    return Err(nom::Err::Failure(ctx_err));
                }
                
                let num_repeats = remaining_coords / repeat_unit_len;
                if let Some(max_r) = signature.max_repeats {
                    if num_repeats > max_r {
                        let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(i, nom::error::ErrorKind::Verify);
                        let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(i, "Too many repeats for shape", base_err);
                        return Err(nom::Err::Failure(ctx_err));
                    }
                }
            }
        } else if n_coords != min_required {
            let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(i, nom::error::ErrorKind::Verify);
            let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(i, "Exact number of coordinates required for shape", base_err);
            return Err(nom::Err::Failure(ctx_err));
        }
        
        (i, (coords, formats))
    } else {
        // This should never happen if shape_type is properly set
        let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(i, nom::error::ErrorKind::Verify);
        let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(i, "Internal error: signature missing for known shape", base_err);
        return Err(nom::Err::Failure(ctx_err));
    };
    
    // Parse optional properties and tags
    let (i, (properties, tags)) = parse_optional_shape_properties_and_tags(i)?;
    
    Ok((i, (exclude, shape_type, coords, formats, properties, tags))) 
}


// --- Main Line Parsing Logic (Internal Rust) ---
// Represents the different kinds of valid lines we can parse.
#[derive(Debug, PartialEq, Clone)]
pub enum ParsedLine { 
    CoordSysDecl(CoordSystem),
    ShapeDecl {
        coord_system: Option<CoordSystem>,
        exclude: bool,
        shape_type: ShapeType,
        coordinates: Vec<f64>,
        coordinate_formats: Vec<u8>, // Store format as integers
        properties: HashMap<String, AttributeValue>, 
        tags: Vec<String>,
    },
    GlobalAttributes { 
        attributes: HashMap<String, AttributeValue>,
        tags: Vec<String>, 
    },
    Comment(String), 
    Empty, 
}


// This function will be the core logic that `parse_single_region_line_for_rust` uses.
// It returns an IResult to be composable.
fn parse_comment_line<'a>(input: Input<'a>) -> ParserResult<'a, ParsedLine> {
    map(
        preceded(
            nom_char('#'),
            terminated(
                opt(not_line_ending),
                opt(line_ending) // Optionally consume a line ending if present
            )
        ),
        |comment_opt: Option<&str>| ParsedLine::Comment(comment_opt.unwrap_or("").trim_start().to_string())
    )(input)
}


fn parse_line_content<'a>(input: Input<'a>, active_system: Option<&'a CoordSystem>) -> ParserResult<'a, ParsedLine> {
    preceded(
        ws, // Consume leading whitespace for the entire line content once
        terminated(
            alt((
                // 1. Comment line (starts with # AFTER initial ws)
                parse_comment_line,
                // 2. Global attribute line
                map(parse_global_line, |(attributes, tags)| ParsedLine::GlobalAttributes { attributes, tags }),
                // 3. COORD_SYSTEM ; SHAPE_DEFINITION
                map(
                    tuple((
                        parse_coord_system_command,
                        preceded(ws, nom_char(';')),
                        preceded(ws, |i| parse_shape_and_props(i, active_system)) // Pass the active system for coordinate parsing
                    )),
                    |(cs, _, (exclude, st, coords, formats, props, tags))| ParsedLine::ShapeDecl {
                        coord_system: Some(cs), // Use the cs parsed in this branch
                        exclude,
                        shape_type: st,
                        coordinates: coords,
                        coordinate_formats: formats, // Include format information
                        properties: props,
                        tags,
                    }
                ),
                // 4. COORD_SYSTEM (alone on a line) - Moved up before shape parsing
                // This parser specifically handles coordinate systems that are alone on a line
                map(
                    terminated(parse_coord_system_command, ws),
                    ParsedLine::CoordSysDecl
                ),
                // 5. SHAPE_DEFINITION (alone on a line) - Use the active coordinate system
                map(
                    |i| parse_shape_and_props(i, active_system), // Pass the active system for coordinate parsing
                    |(exclude, st, coords, formats, props, tags)| ParsedLine::ShapeDecl {
                        coord_system: None,
                        exclude,
                        shape_type: st,
                        coordinates: coords,
                        coordinate_formats: formats, // Include format information
                        properties: props,
                        tags,
                    }
                ),
                // 6. Empty line (only eof after ws)
                map(eof, |_| ParsedLine::Empty)
            )),
            opt(line_ending) // Optionally consume a line ending if present
        )
    )(input)
}


// --- Main Parsing Function (for Rust usage, returns Result) ---
pub fn parse_single_region_line_for_rust(line: &str, active_system: Option<&CoordSystem>) -> Result<(ParsedLine, Option<CoordSystem>), String> { 
    match terminated(|i| parse_line_content(i, active_system), eof)(line).finish() {
        Ok((_, output)) => {
            // Extra validation to catch edge cases
            if matches!(output, ParsedLine::Empty) && !line.trim().is_empty() && !line.trim().starts_with('#') {
                return Err(format!("Line parsed as Empty but was not truly empty or comment: '{}'", line));
            }
            
            // Update the active coordinate system if this line declares one
            let new_active_system = match &output {
                ParsedLine::CoordSysDecl(cs) => Some(cs.clone()),
                ParsedLine::ShapeDecl { coord_system, .. } => coord_system.clone(),
                _ => None,
            };
            
            // Return the parsed line and the potentially updated coordinate system
            // If this line doesn't specify a coordinate system, keep the existing one
            let final_system = new_active_system.or_else(|| active_system.cloned());
            Ok((output, final_system))
        },
        Err(e) => Err(nom::error::convert_error(line, e)),
    }
}

// --- Python Function ---
#[pyfunction]
fn parse_region_line(py: Python<'_>, line: &str, active_system_str: Option<&str>) -> PyResult<PyObject> { 
    // Convert the Python active_system_str to a Rust CoordSystem if provided
    let active_system = active_system_str.map(|s| CoordSystem::from_str(s));
    
    match parse_single_region_line_for_rust(line, active_system.as_ref()) {
        Ok((parsed_line, new_active_system)) => {
            // Convert the new active system to a Python string if it exists
            let py_new_active_system = new_active_system.map(|cs| cs.to_string_py()).into_py(py);
            
            match parsed_line {
                ParsedLine::CoordSysDecl(cs) => {
                    // For CoordSysDecl, the new active system is always the declared system
                    let result_elements: [PyObject; 5] = [cs.to_string_py().into_py(py), py.None(), py.None(), py.None(), py_new_active_system];
                    Ok(PyTuple::new_bound(py, &result_elements).into_py(py))
                }
                ParsedLine::ShapeDecl{ coord_system, exclude, shape_type, coordinates, coordinate_formats, properties, tags } => {
                    let py_coord_system = coord_system.map(|cs| cs.to_string_py()).into_py(py);
                                        
                    let py_props_dict = PyDict::new_bound(py);
                    for (k, v_enum) in properties {
                        let py_val = match v_enum {
                            AttributeValue::String(s) => s.into_py(py),
                            AttributeValue::Number(n) => n.into_py(py),
                            AttributeValue::NumberList(nl) => nl.into_py(py),
                            AttributeValue::Flag(b) => b.into_py(py),
                        };
                        py_props_dict.set_item(k, py_val)?;
                    }
                    
                    let shape_obj = Shape::new(
                        shape_type.to_string_py(),
                        coordinates,
                        Some(coordinate_formats), // Include the format information
                        Some(&py_props_dict), 
                        tags,
                        exclude,
                    )?;
                    let py_shape = Py::new(py, shape_obj)?;

                    let result_elements: [PyObject; 5] = [py_coord_system, py_shape.into_py(py), py.None(), py.None(), py_new_active_system];
                    Ok(PyTuple::new_bound(py, &result_elements).into_py(py))
                }
                ParsedLine::GlobalAttributes{attributes, tags} => {
                    let py_attrs = PyDict::new_bound(py);
                    for (k, v_enum) in attributes {
                        let py_val = match v_enum {
                            AttributeValue::String(s) => s.into_py(py),
                            AttributeValue::Number(n) => n.into_py(py),
                            AttributeValue::NumberList(nl) => nl.into_py(py),
                            AttributeValue::Flag(b) => b.into_py(py),
                        };
                        py_attrs.set_item(k, py_val)?;
                    }
                    if !tags.is_empty() {
                        py_attrs.set_item("tags", tags.into_py(py))?;
                    }
                    let result_elements: [PyObject; 5] = [py.None(), py.None(), py_attrs.into_py(py), py.None(), py_new_active_system];
                    Ok(PyTuple::new_bound(py, &result_elements).into_py(py))
                }
                ParsedLine::Comment(comment_text) => {
                    let result_elements: [PyObject; 5] = [py.None(), py.None(), py.None(), comment_text.into_py(py), py_new_active_system];
                    Ok(PyTuple::new_bound(py, &result_elements).into_py(py))
                }
                ParsedLine::Empty => {
                    let result_elements: [PyObject; 5] = [py.None(), py.None(), py.None(), py.None(), py_new_active_system];
                     Ok(PyTuple::new_bound(py, &result_elements).into_py(py))
                }
            }
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
    
    // Add the coordinate format classes
    // Export format constants to Python
    m.add("FORMAT_SIMPLE", semantic_parsers::FORMAT_SIMPLE)?;
    m.add("FORMAT_SEXAGESIMAL_COLON", semantic_parsers::FORMAT_SEXAGESIMAL_COLON)?;
    m.add("FORMAT_SEXAGESIMAL_HMS", semantic_parsers::FORMAT_SEXAGESIMAL_HMS)?;
    m.add("FORMAT_SEXAGESIMAL_DMS", semantic_parsers::FORMAT_SEXAGESIMAL_DMS)?;
    m.add("FORMAT_WITH_UNIT", semantic_parsers::FORMAT_WITH_UNIT)?;
    
    Ok(())
}

// --- Unit Tests (Rust tests) ---
#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_rust_parses_line {
        // For ShapeDecl
        ($input:expr, $cs:expr, $st:expr, $excl:expr, $num_coords:expr, $num_props:expr, $num_tags:expr) => {
            let result = parse_single_region_line_for_rust($input, None);
            assert!(result.is_ok(), "Internal parsing failed for '{}': {:?}", $input, result.err());
            if let Ok((ParsedLine::ShapeDecl{coord_system, exclude, shape_type, coordinates, coordinate_formats: _, properties, tags}, _)) = result {
                assert_eq!(coord_system, $cs, "Coord system mismatch for '{}'", $input);
                assert_eq!(shape_type, $st, "Shape type mismatch for '{}'", $input);
                assert_eq!(exclude, $excl, "Exclude flag mismatch for '{}'", $input);
                assert_eq!(coordinates.len(), $num_coords, "Coordinate count mismatch for '{}'", $input);
                assert_eq!(properties.len(), $num_props, "Properties count mismatch for '{}'", $input);
                assert_eq!(tags.len(), $num_tags, "Tags count mismatch for '{}'", $input);
            } else {
                panic!("Expected ShapeDecl for '{}', got {:?}", $input, result.unwrap());
            }
        };
        // For CoordSysOnly
        ($input:expr, $cs:expr, CoordSysOnly) => {
            let result = parse_single_region_line_for_rust($input, None);
            assert!(result.is_ok(), "Internal parsing failed for '{}': {:?}", $input, result.err());
            if let Ok((ParsedLine::CoordSysDecl(cs), _)) = result {
                assert_eq!(cs, $cs, "Coord system mismatch for '{}'", $input);
            } else {
                panic!("Expected CoordSysDecl for '{}', got {:?}", $input, result.unwrap());
            }
        };
        // For Comment
        ($input:expr, Comment, $expected_comment:expr) => {
            let result = parse_single_region_line_for_rust($input, None);
            assert!(result.is_ok(), "Internal parsing failed for '{}': {:?}", $input, result.err());
            if let Ok((ParsedLine::Comment(comment_text), _)) = result {
                assert_eq!(comment_text, $expected_comment, "Comment text mismatch for '{}'", $input);
            } else {
                panic!("Expected Comment for '{}', got {:?}", $input, result.unwrap());
            }
        };
        // For GlobalAttributes
        ($input:expr, GlobalAttrs, $num_attrs:expr, $num_tags:expr) => {
            let result = parse_single_region_line_for_rust($input, None);
            assert!(result.is_ok(), "Internal parsing failed for '{}': {:?}", $input, result.err());
            if let Ok((ParsedLine::GlobalAttributes{attributes, tags}, _)) = result {
                assert_eq!(attributes.len(), $num_attrs, "Global attributes count mismatch for '{}'", $input);
                assert_eq!(tags.len(), $num_tags, "Global tags count mismatch for '{}'", $input);
            } else {
                panic!("Expected GlobalAttributes for '{}', got {:?}", $input, result.unwrap());
            }
        };
        // For Empty
        ($input:expr, EmptyLine) => {
            let result = parse_single_region_line_for_rust($input, None);
            assert!(result.is_ok(), "Internal parsing failed for '{}': {:?}", $input, result.err());
            if let Ok((parsed, _)) = result {
                assert!(matches!(parsed, ParsedLine::Empty), "Expected Empty for '{}', got {:?}", $input, parsed);
            } else {
                panic!("Expected Empty for '{}', got error: {:?}", $input, result.err());
            }
        };
    }


     macro_rules! assert_rust_fails {
        ($input:expr) => {
            let result = parse_single_region_line_for_rust($input, None);
             if result.is_ok() {
                 if let Ok((ParsedLine::Empty, _)) = result {
                      if !$input.trim().is_empty() && !$input.trim().starts_with('#') { 
                        panic!("Internal parsing should have failed for '{}' but succeeded with Empty", $input);
                      }
                 } else if let Ok((ParsedLine::Comment(_), _)) = result {
                     if !$input.trim().starts_with('#') { 
                        panic!("Internal parsing should have failed for '{}' but succeeded as Comment: {:?}", $input, result.unwrap());
                     }
                 }
                 else { 
                    panic!("Internal parsing should have failed for '{}' but succeeded with: {:?}", $input, result.unwrap());
                 }
             }
             assert!(result.is_err());
        };
    }

    #[test]
    fn test_rust_parse_comment_lines() {
        assert_rust_parses_line!("# this is a comment", Comment, "this is a comment");
        assert_rust_parses_line!("   # another comment with leading space", Comment, "another comment with leading space");
        assert_rust_parses_line!("#comment_no_space_after_hash", Comment, "comment_no_space_after_hash");
        assert_rust_parses_line!("#", Comment, ""); 
    }

    #[test]
    fn test_rust_parse_empty_lines() {
        assert_rust_parses_line!("", EmptyLine);
        assert_rust_parses_line!("     ", EmptyLine);
    }


    #[test]
    fn test_rust_parse_coord_system_only() {
        assert_rust_parses_line!("fk5", CoordSystem::Fk5, CoordSysOnly);
        assert_rust_parses_line!(" IMAGE ", CoordSystem::Image, CoordSysOnly);
    }

    #[test]
    fn test_rust_parse_coord_system_with_shape() {
        assert_rust_parses_line!("fk5; circle(1,2,3)", Some(CoordSystem::Fk5), ShapeType::Circle, false, 3, 0, 0);
        assert_rust_parses_line!(" J2000 ; point(10,20) # text={test}", Some(CoordSystem::J2000), ShapeType::Point, false, 2, 1, 0);
        assert_rust_parses_line!("fk4; -circle(1,2,3)", Some(CoordSystem::Fk4), ShapeType::Circle, true, 3, 0, 0);
    }
    
    #[test]
    fn test_rust_parse_with_newline_at_end() {
        // Test coordinate system with newline
        assert_rust_parses_line!("fk5\n", CoordSystem::Fk5, CoordSysOnly);
        
        // Test shape with newline
        assert_rust_parses_line!("circle(100,200,30)\n", None, ShapeType::Circle, false, 3, 0, 0);
        
        // Test coordinate system with shape and newline
        assert_rust_parses_line!("fk5; circle(1,2,3)\n", Some(CoordSystem::Fk5), ShapeType::Circle, false, 3, 0, 0);
        
        // Test empty line with newline
        assert_rust_parses_line!("\n", EmptyLine);
        
        // Test comment with newline
        assert_rust_parses_line!("# comment\n", Comment, "comment");
    }
    
    #[test]
    fn test_active_system_propagation() {
        // Test that the active coordinate system is properly propagated
        
        // First, parse a line with a coordinate system declaration
        let result1 = parse_single_region_line_for_rust("fk5", None);
        assert!(result1.is_ok(), "Failed to parse coordinate system declaration");
        
        // Extract the new active coordinate system
        let (_, active_system) = result1.unwrap();
        assert!(active_system.is_some(), "Active system should be Some after parsing coordinate system declaration");
        
        // Use as_ref() to avoid consuming the value when checking
        if let Some(ref cs) = active_system {
            assert_eq!(cs, &CoordSystem::Fk5, "Active system should be FK5");
        } else {
            panic!("Active system should not be None");
        }
        
        // Now parse a shape without an explicit coordinate system, using the active system from before
        let result2 = parse_single_region_line_for_rust("circle(10,20,30)", active_system.as_ref());
        assert!(result2.is_ok(), "Failed to parse shape with active system");
        
        // The shape should be parsed with the active coordinate system
        if let Ok((ParsedLine::ShapeDecl { coord_system, .. }, _)) = result2 {
            assert!(coord_system.is_none(), "Shape's explicit coordinate system should be None");
            // The active system is still propagated separately
        } else {
            panic!("Expected ShapeDecl");
        }
        
        // Test that a new coordinate system declaration overrides the active system
        let result3 = parse_single_region_line_for_rust("j2000", active_system.as_ref());
        assert!(result3.is_ok(), "Failed to parse new coordinate system declaration");
        
        let (_, new_active_system) = result3.unwrap();
        assert!(new_active_system.is_some(), "New active system should be Some");
        assert_eq!(new_active_system.unwrap(), CoordSystem::J2000, "New active system should be J2000");
    }
    
    #[test]
    fn test_rust_parse_shape_only_no_coord_system() {
         assert_rust_parses_line!("circle(100, 200, 30)", None, ShapeType::Circle, false, 3, 0, 0);
         assert_rust_parses_line!("-ellipse(1,2,3,4,5)", None, ShapeType::Ellipse, true, 5, 0, 0);
    }
    
    #[test]
    fn test_rust_parse_global_attributes() {
        let line = r#"global color=green dashlist=8 3 width=1 font="helvetica 10 normal" select=1 highlite=0"#;
        // First, check the basic structure with the macro
        assert_rust_parses_line!(line, GlobalAttrs, 6, 0); // 6 attributes, 0 tags
        
        // Then manually check the specific attribute values
        let result = parse_single_region_line_for_rust(line, None);
        assert!(result.is_ok());
        if let Ok((ParsedLine::GlobalAttributes{attributes, ..}, _)) = result {
            assert_eq!(attributes.get("color"), Some(&AttributeValue::String("green".to_string())));
            assert_eq!(attributes.get("dashlist"), Some(&AttributeValue::NumberList(vec![8.0, 3.0])));
            assert_eq!(attributes.get("width"), Some(&AttributeValue::Number(1.0)));
            assert_eq!(attributes.get("font"), Some(&AttributeValue::String("helvetica 10 normal".to_string())));
            assert_eq!(attributes.get("select"), Some(&AttributeValue::Flag(true)));
            assert_eq!(attributes.get("highlite"), Some(&AttributeValue::Flag(false)));
        } else {
            panic!("Expected GlobalAttributes");
        }
    }
     #[test]
    fn test_rust_parse_global_attributes_single() {
        // Test color=blue
        let line1 = "global color=blue";
        assert_rust_parses_line!(line1, GlobalAttrs, 1, 0);
        
        let result1 = parse_single_region_line_for_rust(line1, None);
        assert!(result1.is_ok());
        if let Ok((ParsedLine::GlobalAttributes{attributes, ..}, _)) = result1 {
            assert_eq!(attributes.get("color"), Some(&AttributeValue::String("blue".to_string())));
        } else {
            panic!("Expected GlobalAttributes for color=blue");
        }
        
        // Test dash=1
        let line2 = "global dash=1";
        assert_rust_parses_line!(line2, GlobalAttrs, 1, 0);
        
        let result2 = parse_single_region_line_for_rust(line2, None);
        assert!(result2.is_ok());
        if let Ok((ParsedLine::GlobalAttributes{attributes, ..}, _)) = result2 {
            assert_eq!(attributes.get("dash"), Some(&AttributeValue::Flag(true)));
        } else {
            panic!("Expected GlobalAttributes for dash=1");
        }
    }


    #[test]
    fn test_excluded_shape_with_properties() {
        assert_rust_parses_line!("-box(1,2,3,4,5) # color=blue", None, ShapeType::Box, true, 5, 1, 0);
    }

    #[test]
    fn test_excluded_shape_leading_whitespace() {
        assert_rust_parses_line!("  - circle(1,2,3)", None, ShapeType::Circle, true, 3, 0, 0);
    }

    #[test]
    fn test_excluded_shape_no_leading_whitespace_before_minus() {
         assert_rust_parses_line!("-circle(10,20,5)", None, ShapeType::Circle, true, 3, 0, 0);
    }


    #[test]
    fn test_rust_parse_simple_circle() {
        let line = "circle(100, 200, 30)";
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 0, 0);
    }

    #[test]
    fn test_rust_parse_polygon_valid() {
        let line = "polygon(1,2,3,4,5,6)"; // 3 pairs
        assert_rust_parses_line!(line, None, ShapeType::Polygon, false, 6, 0, 0);
    }

    #[test]
    fn test_rust_parse_polygon_invalid_count() {
        let line_too_few = "polygon(1,2,3,4)"; 
        assert_rust_fails!(line_too_few);
        let line_misaligned = "polygon(1,2,3,4,5,6,7)"; 
        assert_rust_fails!(line_misaligned);
    }

    #[test]
    fn test_rust_parse_box_valid() {
        let line = "box(1,2,10,20,0)";
        assert_rust_parses_line!(line, None, ShapeType::Box, false, 5,0,0);
    }
     #[test]
    fn test_rust_parse_rotbox_valid() {
        let line = "rotbox(1,2,10,20,30)";
        assert_rust_parses_line!(line, None, ShapeType::RotBox, false, 5,0,0);
    }


    #[test]
    fn test_rust_parse_annulus_valid() {
        let line_3_params = "annulus(1,2,10)"; 
        assert_rust_parses_line!(line_3_params, None, ShapeType::Annulus, false, 3, 0,0);
    }

    #[test]
    fn test_rust_parse_annulus_invalid() {
        let line_too_few = "annulus(1,2)"; 
        assert_rust_fails!(line_too_few);
    }


    #[test]
    fn test_rust_parse_circle_with_whitespace() {
        let line = "  circle  ( 100.5 ,  200 , 30 )   ";
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 0,0);
    }

    #[test]
    fn test_rust_parse_circle_with_properties() {
        let line = "circle( 10.5, 20 , 5.0 ) # color=red width=2 tag={foo}"; 
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 2, 1); 
         match parse_single_region_line_for_rust(line, None) {
              Ok((ParsedLine::ShapeDecl{properties, tags, ..}, _)) => { 
                  assert_eq!(properties.get("color"), Some(&AttributeValue::String("red".to_string())));
                  assert_eq!(properties.get("width"), Some(&AttributeValue::Number(2.0)));
                  assert_eq!(tags.len(), 1);
                  assert_eq!(tags[0], "foo");
              },
              _ => panic!("Should have parsed successfully with shape data"),
          }
    }

    #[test]
    fn test_rust_parse_ellipse() {
        let line = "ellipse(500, 500, 20.1, 10.9, 45)";
        assert_rust_parses_line!(line, None, ShapeType::Ellipse, false, 5, 0,0);
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
        // Use a more flexible approach to check the shape type
        let result = parse_single_region_line_for_rust(line, None);
        assert!(result.is_ok());
        if let Ok((ParsedLine::ShapeDecl{shape_type, ..}, _)) = result {
            match shape_type {
                ShapeType::Unsupported(name) => assert_eq!(name, "someunknownshape"),
                _ => panic!("Expected Unsupported shape type")
            }
        } else {
            panic!("Expected ShapeDecl");
        };
         match parse_single_region_line_for_rust(line, None) {
             Ok((ParsedLine::ShapeDecl{exclude, shape_type, properties, ..}, _)) => {
                 assert!(!exclude);
                 match shape_type {
                     ShapeType::Unsupported(s) => assert!(s.eq_ignore_ascii_case("someunknownshape")),
                     _ => panic!("Expected Unsupported shape type"),
                 }
                 assert_eq!(properties.get("property"), Some(&AttributeValue::String("value".to_string())));
             },
             _ => panic!("Should have parsed successfully with shape data"),
         }
    }
     #[test]
    fn test_rust_vector_shape_defined() {
        let line = "vector(1,2,3,4)";
        assert_rust_parses_line!(line, None, ShapeType::Vector, false, 4,0,0);
    }

    #[test]
    fn test_shape_property_source() {
        let line = "circle(100,100,20) # source";
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 1, 0);
        match parse_single_region_line_for_rust(line, None) {
            Ok((ParsedLine::ShapeDecl { properties, .. }, _)) => {
                assert_eq!(properties.get("source"), Some(&AttributeValue::Flag(true)));
            }
            _ => panic!("Test failed for source property"),
        }
    }

    #[test]
    fn test_shape_property_background() {
        let line = "circle(200,200,10) # background";
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 1, 0);
        match parse_single_region_line_for_rust(line, None) {
            Ok((ParsedLine::ShapeDecl { properties, .. }, _)) => {
                assert_eq!(properties.get("background"), Some(&AttributeValue::Flag(true)));
            }
            _ => panic!("Test failed for background property"),
        }
    }

    #[test]
    fn test_shape_property_multiple_tags() {
        let line = "circle(100,100,20) # tag={Group 1} tag={Group 2}";
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 0, 2); // 0 regular properties, 2 tags
        match parse_single_region_line_for_rust(line, None) {
            Ok((ParsedLine::ShapeDecl { tags, .. }, _)) => {
                assert_eq!(tags.len(), 2);
                assert_eq!(tags[0], "Group 1");
                assert_eq!(tags[1], "Group 2");
            }
            _ => panic!("Test failed for multiple tags"),
        }
    }
     #[test]
    fn test_shape_property_text_with_curly_braces() {
        let line = r#"circle(100,100,20) # text={This message has both a " and ' in it}"#;
        assert_rust_parses_line!(line, None, ShapeType::Circle, false, 3, 1, 0);
        match parse_single_region_line_for_rust(line, None) {
            Ok((ParsedLine::ShapeDecl { properties, .. }, _)) => {
                assert_eq!(properties.get("text"), Some(&AttributeValue::String(r#"This message has both a " and ' in it"#.to_string())));
            }
            _ => panic!("Test failed for text property with curly braces"),
        }
    }


}
