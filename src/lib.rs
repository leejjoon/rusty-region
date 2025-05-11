//! # Rusty Region
//!
//! A parser for DS9 region files, written in Rust using nom 7.1.
//! This library provides tools to parse region file strings into structured data.
//! Includes Python bindings via PyO3.

// --- PyO3 Imports ---
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError;

// --- Nom Imports ---
use nom::{
    IResult,
    character::complete::{alphanumeric1, multispace0, multispace1, char as nom_char},
    bytes::complete::take_while1,
    combinator::{map, map_res, opt}, // Added map_res
    sequence::{preceded, terminated, separated_pair, tuple},
    multi::{separated_list0, separated_list1},
    number::complete::double,
    error::{VerboseError, context, ParseError as NomParseErrorTrait, ContextError}, // Added ContextError trait
    Finish,
    Parser,
};
use std::collections::HashMap; // For storing shape definitions

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
fn ws<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { multispace0(input) }
fn ws1<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> { multispace1(input) }

fn parse_f64<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    context("floating point number", preceded(ws, terminated(double, ws)))(input)
}

fn parse_identifier_str<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    context("identifier", preceded(ws, terminated(alphanumeric1, ws)))(input)
}

// --- Component Parsers ---
fn parse_coordinates_list_f64<'a>(input: Input<'a>) -> ParserResult<'a, Vec<f64>> {
    context(
        "coordinate list",
        preceded(
            context("opening parenthesis", tuple((ws, nom_char('(')))),
            terminated(
                nom::multi::separated_list1(
                    context("coordinate separator comma", tuple((ws, nom_char(','), ws))),
                    parse_f64
                ),
                context("closing parenthesis", tuple((ws, nom_char(')'))))
            )
        )
    )(input)
}

fn parse_property_value_str<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    context("property value", take_while1(|c: char| !c.is_whitespace() && c != '#'))(input)
}

fn parse_property_internal<'a>(input: Input<'a>) -> ParserResult<'a, Property> {
    context(
        "property",
        map(
            separated_pair(
                parse_identifier_str,
                tuple((ws, nom_char('='), ws)),
                parse_property_value_str
            ),
            |(k, v)| Property { key: k.to_string(), value: v.to_string() }
        )
    )(input)
}

fn parse_optional_properties_internal<'a>(input: Input<'a>) -> ParserResult<'a, Vec<Property>> {
    context(
        "optional properties",
        map(
            opt(
                preceded(
                    context("property marker '#'", tuple((ws, nom_char('#'), ws1))),
                    nom::multi::separated_list0(ws1, parse_property_internal)
                )
            ),
            |opt_props| opt_props.unwrap_or_else(Vec::new)
        )
    )(input)
}

// --- Shape Definition Logic ---

/// Returns the expected coordinate signature for a given shape name.
/// Based on the Python ds9_shape_defs and user clarification.
fn get_shape_signature(shape_name_lc: &str) -> Option<ShapeSignature> {
    use SemanticCoordType::*;
    // Helper to quickly define static slices
    macro_rules! sct_slice { ($($x:expr),* $(,)?) => { &[$($x),*] } }

    match shape_name_lc {
        "circle" => Some(ShapeSignature {
            name: "circle",
            fixed_head: sct_slice![CoordOdd, CoordEven, Distance],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "ellipse" => Some(ShapeSignature {
            name: "ellipse",
            fixed_head: sct_slice![CoordOdd, CoordEven, Distance, Distance, Angle],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "box" | "rotbox" => Some(ShapeSignature {
            name: if shape_name_lc == "box" { "box" } else { "rotbox" },
            fixed_head: sct_slice![CoordOdd, CoordEven],
            repeat_unit: Some(sct_slice![Distance, Distance]),
            min_repeats: 1,
            max_repeats: Some(1),
            fixed_tail: sct_slice![Angle],
        }),
        "polygon" => Some(ShapeSignature {
            name: "polygon",
            fixed_head: sct_slice![],
            repeat_unit: Some(sct_slice![CoordOdd, CoordEven]),
            min_repeats: 3,
            max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "point" => Some(ShapeSignature {
            name: "point",
            fixed_head: sct_slice![CoordOdd, CoordEven],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "line" => Some(ShapeSignature {
            name: "line",
            fixed_head: sct_slice![CoordOdd, CoordEven, CoordOdd, CoordEven],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "annulus" => Some(ShapeSignature {
            name: "annulus",
            fixed_head: sct_slice![CoordOdd, CoordEven],
            repeat_unit: Some(sct_slice![Distance]),
            min_repeats: 1,
            max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "pie" => Some(ShapeSignature {
            name: "pie",
            fixed_head: sct_slice![CoordOdd, CoordEven, Distance, Distance, Angle, Angle],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "vector" => Some(ShapeSignature {
            name: "vector",
            fixed_head: sct_slice![CoordOdd, CoordEven, Distance, Angle],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "text" => Some(ShapeSignature {
            name: "text",
            fixed_head: sct_slice![CoordOdd, CoordEven],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "panda" => Some(ShapeSignature {
            name: "panda",
            fixed_head: sct_slice![CoordOdd, CoordEven, Angle, Angle, Integer, Distance, Distance, Integer],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        "epanda" | "bpanda" => Some(ShapeSignature {
            name: if shape_name_lc == "epanda" { "epanda" } else { "bpanda" },
            fixed_head: sct_slice![CoordOdd, CoordEven, Angle, Angle, Integer, Distance, Distance, Distance, Distance, Integer, Angle],
            repeat_unit: None, min_repeats: 0, max_repeats: None,
            fixed_tail: sct_slice![],
        }),
        _ => None,
    }
}


// --- Shape Parser (Rust internal result) ---
// Returns (ShapeType enum, Vec<f64>, Vec<Property>)
fn parse_shape_definition_internal<'a>(input: Input<'a>) -> ParserResult<'a, (ShapeType, Vec<f64>, Vec<Property>)> {
    context(
        "shape_definition_internal",
        // Use map_res to allow the mapping function to return a Result
        map_res(
            tuple((
                parse_identifier_str,
                parse_coordinates_list_f64,
                parse_optional_properties_internal,
            )),
            // This closure now returns Result<(ShapeType, Vec<f64>, Vec<Property>), nom::Err<NomVerboseError<'a>>>
            |(shape_keyword, coords, props): (&str, Vec<f64>, Vec<Property>)| {
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

                if let ShapeType::Unsupported(_) = shape_type_enum {
                    return Ok((shape_type_enum, coords, props));
                }

                let error_input_ref = input; // Use the original input for error location context

                if let Some(signature) = get_shape_signature(&shape_keyword_lc) {
                    let n_coords = coords.len();
                    let len_fixed_head = signature.fixed_head.len();
                    let len_fixed_tail = signature.fixed_tail.len();
                    let min_required_for_fixed = len_fixed_head + len_fixed_tail;

                    if n_coords < min_required_for_fixed {
                        let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                        let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "coordinate count validation (fixed parts)", base_err);
                        return Err(nom::Err::Error(ctx_err));
                    }

                    if let Some(repeat_unit_slice) = signature.repeat_unit {
                        let len_repeat_unit = repeat_unit_slice.len();
                        if len_repeat_unit == 0 {
                            let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                            let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "coordinate count validation (invalid signature: repeat unit empty)", base_err);
                            return Err(nom::Err::Error(ctx_err));
                        }

                        let n_repeating_coords = n_coords - min_required_for_fixed;

                        if n_repeating_coords < signature.min_repeats * len_repeat_unit {
                             let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                            let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "coordinate count validation (min repeats)", base_err);
                            return Err(nom::Err::Error(ctx_err));
                        }

                        if n_repeating_coords % len_repeat_unit != 0 {
                            let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                            let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "coordinate count validation (repeat alignment)", base_err);
                            return Err(nom::Err::Error(ctx_err));
                        }

                        let num_repeats = n_repeating_coords / len_repeat_unit;
                        if let Some(max_r) = signature.max_repeats {
                            if num_repeats > max_r {
                                let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                                let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "coordinate count validation (max repeats)", base_err);
                                return Err(nom::Err::Error(ctx_err));
                            }
                        }
                    } else { // No repeating part defined
                        if n_coords != min_required_for_fixed {
                            let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                            let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "coordinate count validation (exact fixed)", base_err);
                            return Err(nom::Err::Error(ctx_err));
                        }
                    }
                } else {
                    let base_err = <NomVerboseError<'a> as NomParseErrorTrait<Input<'a>>>::from_error_kind(error_input_ref, nom::error::ErrorKind::Verify);
                    let ctx_err = <NomVerboseError<'a> as nom::error::ContextError<Input<'a>>>::add_context(error_input_ref, "internal signature missing", base_err);
                    return Err(nom::Err::Error(ctx_err));
                }
                Ok((shape_type_enum, coords, props))
            }
        )
    )(input)
}

// --- Main Parsing Function (for Rust usage, returns Result) ---
pub fn parse_single_region_line_for_rust(line: &str) -> Result<(ShapeType, Vec<f64>, Vec<Property>), String> {
    match terminated(preceded(ws, parse_shape_definition_internal), ws)(line).finish() {
        Ok((_remaining, output)) => Ok(output),
        Err(e) => Err(nom::error::convert_error(line, e)),
    }
}

// --- Python Function ---
#[pyfunction]
fn parse_region_line(py: Python<'_>, line: &str) -> PyResult<Py<Shape>> {
    match parse_single_region_line_for_rust(line) {
        Ok((shape_type_rust, coords_rust, props_rust)) => {
            let props_py: Vec<Py<Property>> = props_rust
                .into_iter()
                .map(|p_rust| Py::new(py, p_rust))
                .collect::<PyResult<_>>()?;

            let shape_obj = Shape::new(
                shape_type_rust.to_string_py(),
                coords_rust,
                props_py,
            );
            Py::new(py, shape_obj)
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

     macro_rules! assert_rust_parses {
        ($input:expr, $expected_type:pat, $expected_coords_len:expr, $expected_props_len:expr) => {
            match parse_single_region_line_for_rust($input) {
                Ok((shape_type, coords, props)) => {
                    assert!(matches!(shape_type, $expected_type), "Shape type mismatch. Got: {:?}", shape_type);
                    assert_eq!(coords.len(), $expected_coords_len, "Coordinate count mismatch for '{}'. Got: {:?}, expected {}", $input, coords, $expected_coords_len);
                    assert_eq!(props.len(), $expected_props_len, "Property count mismatch for '{}'. Got: {:?}, expected {}", $input, props, $expected_props_len);
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
    fn test_rust_parse_simple_circle() {
        let line = "circle(100, 200, 30)";
        assert_rust_parses!(line, ShapeType::Circle, 3, 0);
    }

    #[test]
    fn test_rust_parse_polygon_valid() {
        let line = "polygon(1,2,3,4,5,6)"; // 3 pairs
        assert_rust_parses!(line, ShapeType::Polygon, 6, 0);
        let line2 = "polygon(1,2,3,4,5,6,7,8)"; // 4 pairs
        assert_rust_parses!(line2, ShapeType::Polygon, 8, 0);
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
        assert_rust_parses!(line, ShapeType::Box, 5,0);
    }
     #[test]
    fn test_rust_parse_rotbox_valid() {
        let line = "rotbox(1,2,10,20,30)";
        assert_rust_parses!(line, ShapeType::RotBox, 5,0);
    }


    #[test]
    fn test_rust_parse_annulus_valid() {
        let line_3_params = "annulus(1,2,10)"; // x,y,r_inner
        assert_rust_parses!(line_3_params, ShapeType::Annulus, 3, 0);
        let line_4_params = "annulus(1,2,10,20)"; // x,y,r_inner, r_outer1
        assert_rust_parses!(line_4_params, ShapeType::Annulus, 4, 0);
        let line_5_params = "annulus(1,2,10,20,30)"; // x,y,r_inner, r_outer1, r_outer2
        assert_rust_parses!(line_5_params, ShapeType::Annulus, 5, 0);
    }

    #[test]
    fn test_rust_parse_annulus_invalid() {
        let line_too_few = "annulus(1,2)"; // Needs at least x,y,r_inner
        assert_rust_fails!(line_too_few);
    }


    #[test]
    fn test_rust_parse_circle_with_whitespace() {
        let line = "  circle  ( 100.5 ,  200 , 30 )   ";
        assert_rust_parses!(line, ShapeType::Circle, 3, 0);
    }

    #[test]
    fn test_rust_parse_circle_with_properties() {
        let line = "circle( 10.5, 20 , 5.0 ) # color=red width=2 tag=foo";
        assert_rust_parses!(line, ShapeType::Circle, 3, 3);
         match parse_single_region_line_for_rust(line) {
             Ok((_, _, props)) => {
                 assert_eq!(props[0], Property { key: "color".to_string(), value: "red".to_string() });
                 assert_eq!(props[1], Property { key: "width".to_string(), value: "2".to_string() });
                 assert_eq!(props[2], Property { key: "tag".to_string(), value: "foo".to_string() });
             },
             _ => panic!("Should have parsed successfully"),
         }
    }

    #[test]
    fn test_rust_parse_ellipse() {
        let line = "ellipse(500, 500, 20.1, 10.9, 45)";
        assert_rust_parses!(line, ShapeType::Ellipse, 5, 0);
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
        assert_rust_parses!(line, ShapeType::Unsupported(_), 4, 1);
         match parse_single_region_line_for_rust(line) {
             Ok((shape_type, _, props)) => {
                 match shape_type {
                     ShapeType::Unsupported(s) => assert!(s.eq_ignore_ascii_case("someunknownshape")),
                     _ => panic!("Expected Unsupported shape type"),
                 }
                 assert_eq!(props[0], Property { key: "property".to_string(), value: "value".to_string() });
             },
             _ => panic!("Should have parsed successfully"),
         }
    }
     #[test]
    fn test_rust_vector_shape_defined() {
        let line = "vector(1,2,3,4)";
        assert_rust_parses!(line, ShapeType::Vector, 4,0);
    }


}
