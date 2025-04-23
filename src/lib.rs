//! # Rusty Region
//!
//! A parser for DS9 region files, written in Rust using nom 7.1.
//! This library provides tools to parse region file strings into structured data.
//! Includes Python bindings via PyO3.

// --- PyO3 Imports ---
use pyo3::prelude::*;
use pyo3::exceptions::PyValueError; // For raising Python errors
// use pyo3::types::PyList; // Unused

// --- Module Imports ---
use nom::{
    IResult, // Standard nom result type: Result<(Input, Output), Err<Error>>
    // Err as NomErr, // Unused
    character::complete::{alphanumeric1, multispace0, multispace1, char as nom_char}, // Removed unused space1
    bytes::complete::{take_while1}, // Removed unused tag
    combinator::{map, opt}, // Removed unused value
    sequence::{preceded, terminated, separated_pair, tuple}, // Sequence combinators
    multi::{separated_list0, separated_list1}, // List combinators
    number::complete::double, // Floating point number parser
    // branch::alt, // Unused
    error::{VerboseError, context}, // Renamed trait import
    Finish, // Used to convert IResult to standard Result and ensure full consumption
    // Parser, // Unused
};

// --- Custom Error Type (Optional but recommended for better errors) ---
// Using nom's VerboseError for potentially more detailed debugging info.
// You could define your own enum implementing nom::error::ParseError.
type Error<'a> = VerboseError<&'a str>;

// --- Data Structures ---

/// Represents the type of a geometric shape found in a region file.
// Note: This is kept as a Rust enum internally. We'll convert it to a string for Python.
#[derive(Debug, PartialEq, Clone)]
pub enum ShapeType {
    Circle,
    Ellipse,
    Box,
    Polygon,
    Point,
    Line,
    Unsupported(String),
}

impl ShapeType {
    /// Converts the enum variant to a string representation.
    fn to_string_py(&self) -> String {
        match self {
            ShapeType::Circle => "circle".to_string(),
            ShapeType::Ellipse => "ellipse".to_string(),
            ShapeType::Box => "box".to_string(),
            ShapeType::Polygon => "polygon".to_string(),
            ShapeType::Point => "point".to_string(),
            ShapeType::Line => "line".to_string(),
            ShapeType::Unsupported(s) => format!("unsupported({})", s),
        }
    }

    /// Converts a string back to the enum variant (basic implementation).
    fn from_string_py(s: &str) -> Self {
        match s {
            "circle" => ShapeType::Circle,
            "ellipse" => ShapeType::Ellipse,
            "box" => ShapeType::Box,
            "polygon" => ShapeType::Polygon,
            "point" => ShapeType::Point,
            "line" => ShapeType::Line,
            // Basic handling for unsupported, might need refinement
            _ if s.starts_with("unsupported(") && s.ends_with(')') => {
                ShapeType::Unsupported(s["unsupported(".len()..s.len()-1].to_string())
            }
            _ => ShapeType::Unsupported(s.to_string()), // Default fallback
        }
    }
}


/// Represents a key-value property associated with a shape (e.g., color=red, width=2).
// Expose this struct to Python using #[pyclass]
#[pyclass(get_all)] // get_all automatically creates Python getters for fields
#[derive(Debug, PartialEq, Clone)] // Keep PartialEq for Property itself
pub struct Property {
    // `get_all` provides getters. Add `set` if modification from Python is needed.
    #[pyo3(set)]
    pub key: String,
    #[pyo3(set)]
    pub value: String,
}

// Implement methods for the Property Python class
#[pymethods]
impl Property {
    // Constructor for PyO3
    #[new]
    fn new(key: String, value: String) -> Self {
        Property { key, value }
    }
}

/// Represents a single shape definition from a region file line.
// Expose this struct to Python using #[pyclass]
#[pyclass]
#[derive(Debug, Clone)] // Removed PartialEq due to Py<Property>
pub struct Shape {
    // We need Python-accessible fields. Use #[pyo3(get)] for getters.
    #[pyo3(get)]
    shape_type_str: String, // Store type as string for Python

    #[pyo3(get)]
    coordinates: Vec<f64>,

    #[pyo3(get)]
    properties: Vec<Py<Property>>, // Store properties as Python objects

    // Keep original Rust fields private if needed, or remove if redundant
    // No attribute needed to skip, just don't add #[pyo3(get/set)]
    _internal_shape_type: ShapeType,
}

// Implement methods for the Shape Python class
#[pymethods]
impl Shape {
    // Constructor for PyO3
    // Accepts arguments that can be easily converted from Python types
    #[new]
    fn new(py: Python<'_>, shape_type_str: String, coordinates: Vec<f64>, properties_rust: Vec<Property>) -> PyResult<Self> {
        // Convert Vec<Property> to Vec<Py<Property>> inside the constructor
        let properties_py: Vec<Py<Property>> = properties_rust
            .into_iter()
            .map(|p| Py::new(py, p)) // Create Python instances
            .collect::<PyResult<_>>()?; // Collect into PyResult<Vec<Py<Property>>>

        // Reconstruct the internal enum from the string
        let internal_shape_type = ShapeType::from_string_py(&shape_type_str);

        Ok(Shape {
            shape_type_str,
            coordinates,
            properties: properties_py,
            _internal_shape_type: internal_shape_type,
        })
    }

    // Example method if needed
    // fn __repr__(&self) -> String {
    //     format!("<Shape type='{}' ...>", self.shape_type_str)
    // }
}


// --- Parser Implementation ---

// Define Input type alias for clarity
type Input<'a> = &'a str;
// Define a type alias for nom's IResult using our VerboseError
type ParserResult<'a, O> = IResult<Input<'a>, O, Error<'a>>;

// --- Basic Parsers ---

/// Parses zero or more whitespace characters, returning the input slice.
fn ws<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    multispace0(input)
}

/// Parses one or more whitespace characters, returning the input slice.
fn ws1<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    multispace1(input) // Or use space1 for only spaces/tabs
}


/// Parses a floating point number (f64), consuming surrounding whitespace.
fn parse_f64<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    // Wrap the entire combinator chain with context
    context(
        "floating point number",
        terminated(
            preceded(ws, double), // Use nom's double parser
            ws
        )
    )(input)
}

/// Parses an identifier (alphanumeric string, e.g., shape names, property keys).
fn parse_identifier<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    // Wrap the entire combinator chain with context
    context(
        "identifier (letters/numbers)",
        terminated(
            preceded(ws, alphanumeric1),
            ws
        )
    )(input)
}


// --- Component Parsers ---

/// Parses a list of coordinates enclosed in parentheses: `( N, N, N, ... )`.
fn parse_coordinates<'a>(input: Input<'a>) -> ParserResult<'a, Vec<f64>> {
    // Wrap the entire combinator chain with context
    context(
        "coordinate list in parentheses",
        preceded(
            // Use context function around the parser it describes
            context("opening parenthesis for coordinates", tuple((ws, nom_char('(')))),
            terminated(
                // Use context function around the parser it describes
                context(
                    "comma-separated coordinates list",
                    separated_list1(
                        context("coordinate separator comma", tuple((ws, nom_char(','), ws))), // Separator parser
                        parse_f64 // Item parser
                    )
                ),
                // Use context function around the parser it describes
                context("closing parenthesis for coordinates", tuple((ws, nom_char(')'))))
            )
        )
    )(input)
}

/// Parses a property value.
/// This is still a simplified version.
fn parse_property_value<'a>(input: Input<'a>) -> ParserResult<'a, &'a str> {
    // Wrap the entire combinator chain with context
    context(
        "property value (simple version)",
        // Basic approach: take characters until the next whitespace or '#' or end of input.
        // TODO: Enhance this parser significantly for real-world region files (quotes, braces).
        take_while1(|c: char| !c.is_whitespace() && c != '#')
    )(input)
}

/// Parses a single property: `key=value`. Returns the Rust struct.
fn parse_property<'a>(input: Input<'a>) -> ParserResult<'a, Property> {
    // Wrap the entire combinator chain with context
    context(
        "key=value property",
        // Use map combinator function
        map(
            separated_pair(
                parse_identifier,      // The key (e.g., "color")
                tuple((ws, nom_char('='), ws)), // The separator ("=")
                parse_property_value   // The value (e.g., "red")
            ),
            |(key_str, value_str)| Property { // Convert the parsed strings into a Property struct
                key: key_str.to_string(),
                value: value_str.to_string(),
            }
        )
    )(input)
}


/// Parses the optional properties/comment part after a shape definition. Returns Vec<Property>.
fn parse_optional_properties<'a>(input: Input<'a>) -> ParserResult<'a, Vec<Property>> {
    // Wrap the entire combinator chain with context
    context(
        "optional properties section starting with #",
        // Use map combinator function
        map( // Map the Option<Vec> to Vec
            opt(
                // `preceded` ensures '#' and at least one whitespace character are present
                preceded(
                    context("property marker '#' followed by space", tuple((ws, nom_char('#'), ws1))),
                    // `separated_list0` parses zero or more items separated by whitespace.
                    context(
                        "list of properties",
                        separated_list0(
                            ws1, // Separator is one or more whitespace
                            parse_property // Item parser returns Rust Property struct
                        )
                    )
                )
            ),
            // If `opt` returned `None` (no '#' section), provide an empty Vec.
            // Otherwise, unwrap the `Some(Vec<Property>)`.
            |opt_props| opt_props.unwrap_or_else(Vec::new)
        )
    )(input)
}

// --- Shape Parser ---

/// Parses a full shape definition line (e.g., "circle(10, 20, 5) # color=red").
/// Returns IResult containing the remaining input and the parsed Rust Shape struct data.
pub fn parse_shape_definition<'a>(input: Input<'a>) -> ParserResult<'a, (ShapeType, Vec<f64>, Vec<Property>)> {
    // Wrap the entire combinator chain with context
    context(
        "shape definition",
        // Use map combinator function correctly
        map(
            tuple((
                parse_identifier, // 1. Shape keyword
                parse_coordinates, // 2. Coordinates
                parse_optional_properties // 3. Optional properties after '#'
            )),
            // Map the result tuple into our internal representation
            |(shape_keyword, coords, props)| {
                let shape_type = match shape_keyword.to_lowercase().as_str() {
                    "circle" => ShapeType::Circle,
                    "ellipse" => ShapeType::Ellipse,
                    "box" => ShapeType::Box,
                    "polygon" => ShapeType::Polygon,
                    "point" => ShapeType::Point,
                    "line" => ShapeType::Line,
                    _ => ShapeType::Unsupported(shape_keyword.to_string()),
                };
                (shape_type, coords, props)
            }
        )
    )(input)
}


// --- Main Parsing Function (Internal Rust) ---

/// Parses a single line expected to contain a region shape definition.
/// Handles leading/trailing whitespace and ensures the entire line is consumed.
/// Returns Result<(ShapeType, Vec<f64>, Vec<Property>), String>
pub fn parse_single_region_line_internal(line: &str) -> Result<(ShapeType, Vec<f64>, Vec<Property>), String> {
    // Define the full line parser: optional whitespace, shape definition, optional whitespace, end of input
    let mut parser = terminated(
        preceded(ws, parse_shape_definition), // parse_shape_definition returns the tuple
        ws // Consume trailing whitespace before checking eof implicitly with finish
    );

    match parser(line).finish() {
        Ok((_remaining_input, (shape_type, coords, props))) => {
             Ok((shape_type, coords, props))
        },
        Err(e) => {
            Err(nom::error::convert_error(line, e))
        }
    }
}

// --- Python Function ---

/// Parses a single region line string and returns a Shape object.
/// Raises ValueError on parsing failure.
#[pyfunction]
fn parse_region_line(py: Python<'_>, line: &str) -> PyResult<Py<Shape>> {
    match parse_single_region_line_internal(line) {
        Ok((shape_type, coords, props_rust)) => {
            // Create the Python Shape object using its #[new] constructor
            // Pass the necessary arguments that can be converted from Rust types
            let shape_obj = Shape::new(
                py, // Pass Python context
                shape_type.to_string_py(), // Convert enum to string
                coords,
                props_rust // Pass the Vec<Property> directly
            )?;
            // Wrap the created Rust struct instance in Py<>
            Ok(Py::new(py, shape_obj)?)
        }
        Err(e_str) => {
            // Convert the Rust error string into a Python ValueError
            Err(PyValueError::new_err(e_str))
        }
    }
}


// --- Python Module Definition ---

/// A Python module implemented in Rust for parsing DS9 region files.
#[pymodule]
fn rusty_region_parser(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(parse_region_line, m)?)?;
    m.add_class::<Shape>()?;
    m.add_class::<Property>()?;
    Ok(())
}


// --- Unit Tests (Rust tests remain unchanged) ---
#[cfg(test)]
mod tests {
    use super::*;

    // Test the internal Rust function directly
     macro_rules! assert_internal_parses {
        ($input:expr, $expected_type:pat, $expected_coords:expr, $expected_props_len:expr) => {
            match parse_single_region_line_internal($input) {
                Ok((shape_type, coords, props)) => {
                    assert!(matches!(shape_type, $expected_type), "Shape type mismatch");
                    assert_eq!(coords, $expected_coords, "Coordinate mismatch");
                    assert_eq!(props.len(), $expected_props_len, "Property count mismatch");
                },
                Err(e_str) => panic!("Internal parsing failed for '{}':\n{}", $input, e_str),
            }
        };
    }

     macro_rules! assert_internal_fails {
        ($input:expr) => {
            let result = parse_single_region_line_internal($input);
             if result.is_ok() {
                 panic!("Internal parsing should have failed for '{}' but succeeded with: {:?}", $input, result.unwrap());
             }
             assert!(result.is_err());
        };
    }


    #[test]
    fn test_internal_parse_simple_circle() {
        let line = "circle(100, 200, 30)";
        assert_internal_parses!(line, ShapeType::Circle, vec![100.0, 200.0, 30.0], 0);
    }

     #[test]
    fn test_internal_parse_circle_with_whitespace() {
        let line = "  circle  ( 100.5 ,  200 , 30 )   ";
        assert_internal_parses!(line, ShapeType::Circle, vec![100.5, 200.0, 30.0], 0);
    }


     #[test]
    fn test_internal_parse_circle_with_properties() {
        let line = "circle( 10.5, 20 , 5.0 ) # color=red width=2 tag=foo";
         assert_internal_parses!(line, ShapeType::Circle, vec![10.5, 20.0, 5.0], 3);
         // Could add more detailed property checks here if needed
         match parse_single_region_line_internal(line) {
             Ok((_, _, props)) => {
                 assert_eq!(props[0], Property { key: "color".to_string(), value: "red".to_string() });
                 assert_eq!(props[1], Property { key: "width".to_string(), value: "2".to_string() });
                 assert_eq!(props[2], Property { key: "tag".to_string(), value: "foo".to_string() });
             },
             _ => panic!("Should have parsed successfully"),
         }
    }

      #[test]
    fn test_internal_parse_ellipse() {
        let line = "ellipse(500, 500, 20.1, 10.9, 45)";
        assert_internal_parses!(line, ShapeType::Ellipse, vec![500.0, 500.0, 20.1, 10.9, 45.0], 0);
    }

      #[test]
    fn test_internal_invalid_syntax_missing_coord() {
        let line = "circle(100, 200, )";
        assert_internal_fails!(line);
    }

      #[test]
    fn test_internal_invalid_syntax_unclosed_paren() {
        let line = "circle(100, 200, 30";
        assert_internal_fails!(line);
    }

      #[test]
    fn test_internal_unsupported_shape() {
        let line = "vector(1, 2, 10, 0) # property=value";
         assert_internal_parses!(line, ShapeType::Unsupported(_), vec![1.0, 2.0, 10.0, 0.0], 1);
         match parse_single_region_line_internal(line) {
             Ok((shape_type, _, props)) => {
                 match shape_type {
                     ShapeType::Unsupported(s) => assert!(s.eq_ignore_ascii_case("vector")),
                     _ => panic!("Expected Unsupported shape type"),
                 }
                 assert_eq!(props[0], Property { key: "property".to_string(), value: "value".to_string() });
             },
             _ => panic!("Should have parsed successfully"),
         }
    }

}
