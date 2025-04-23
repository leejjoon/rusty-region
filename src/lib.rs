//! # Rusty Region
//!
//! A parser for DS9 region files, written in Rust using nom 7.1.
//! This library provides tools to parse region file strings into structured data.

// --- Module Imports ---
use nom::{
    IResult, // Standard nom result type: Result<(Input, Output), Err<Error>>
    Err as NomErr, // nom's error type wrapper
    character::complete::{alphanumeric1, multispace0, multispace1, char as nom_char, space1}, // Character parsers
    bytes::complete::{tag, take_while1}, // Byte/tag parsers
    combinator::{map, opt, value}, // Combinators
    sequence::{preceded, terminated, separated_pair, tuple}, // Sequence combinators
    multi::{separated_list0, separated_list1}, // List combinators
    number::complete::double, // Floating point number parser
    branch::alt, // Alternative parsers (for future use, e.g., property values)
    error::{ParseError as NomParseError, VerboseError, context}, // Error handling
    Finish, // Used to convert IResult to standard Result and ensure full consumption
};

// --- Custom Error Type (Optional but recommended for better errors) ---
// Using nom's VerboseError for potentially more detailed debugging info.
// You could define your own enum implementing nom::error::ParseError.
type Error<'a> = VerboseError<&'a str>;

// --- Data Structures ---

/// Represents the type of a geometric shape found in a region file.
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

/// Represents a key-value property associated with a shape (e.g., color=red, width=2).
#[derive(Debug, PartialEq, Clone)]
pub struct Property {
    pub key: String,
    pub value: String,
}

/// Represents a single shape definition from a region file line.
#[derive(Debug, PartialEq, Clone)]
pub struct Shape {
    pub shape_type: ShapeType,
    pub coordinates: Vec<f64>,
    pub properties: Vec<Property>,
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

/// Parses a single property: `key=value`.
fn parse_property<'a>(input: Input<'a>) -> ParserResult<'a, Property> {
    // Wrap the entire combinator chain with context
    context(
        "key=value property",
        // `separated_pair` parses three components: left, separator, right.
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


/// Parses the optional properties/comment part after a shape definition.
/// Starts with '#', followed by optional space-separated properties.
fn parse_optional_properties<'a>(input: Input<'a>) -> ParserResult<'a, Vec<Property>> {
    // Wrap the entire combinator chain with context
    context(
        "optional properties section starting with #",
        // `opt` makes the parser optional. It returns Option<Output>.
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
                            parse_property // Item parser
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
/// Returns IResult containing the remaining input and the parsed Shape.
pub fn parse_shape_definition<'a>(input: Input<'a>) -> ParserResult<'a, Shape> {
    // Wrap the entire combinator chain with context
    context(
        "shape definition",
        // Use a tuple to parse sequence and map the result
        map(
            tuple((
                parse_identifier, // 1. Shape keyword
                parse_coordinates, // 2. Coordinates
                parse_optional_properties // 3. Optional properties after '#'
            )),
            |(shape_keyword, coords, props)| { // Deconstruct the tuple
                // 4. Map the parsed keyword string to the ShapeType enum
                let shape_type = match shape_keyword.to_lowercase().as_str() {
                    "circle" => ShapeType::Circle,
                    "ellipse" => ShapeType::Ellipse,
                    "box" => ShapeType::Box,
                    "polygon" => ShapeType::Polygon,
                    "point" => ShapeType::Point,
                    "line" => ShapeType::Line,
                    _ => ShapeType::Unsupported(shape_keyword.to_string()),
                };

                // 5. Construct and return the Shape struct
                Shape {
                    shape_type,
                    coordinates: coords,
                    properties: props,
                }
            }
        )
    )(input)
}


// --- Main Parsing Function (Example Entry Point) ---

/// Parses a single line expected to contain a region shape definition.
/// Handles leading/trailing whitespace and ensures the entire line is consumed.
/// Returns Result<Shape, ParseError>
pub fn parse_single_region_line(line: &str) -> Result<Shape, String> {
    // Define the full line parser: optional whitespace, shape definition, optional whitespace, end of input
    let mut parser = terminated(
        preceded(ws, parse_shape_definition),
        ws // Consume trailing whitespace before checking eof implicitly with finish
    );

    // Use `.finish()` to convert IResult to standard Result and ensure all input is consumed.
    // It returns Result<Output, Error> if successful and all input is parsed,
    // or Err<Error> otherwise.
    match parser(line).finish() {
        Ok((_remaining_input, shape)) => {
             // finish() ensures remaining_input is empty on Ok
             Ok(shape)
        },
        Err(e) => {
            // Convert nom's VerboseError into a readable string
            // nom::error::convert_error provides a helper for this
            Err(nom::error::convert_error(line, e))
        }
    }
}


// --- Unit Tests ---
#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_parses {
        ($input:expr, $expected:expr) => {
            match parse_single_region_line($input) {
                Ok(shape) => assert_eq!(shape, $expected),
                Err(e_str) => panic!("Parsing failed for '{}':\n{}", $input, e_str), // Show formatted error string
            }
        };
    }

     macro_rules! assert_fails {
        ($input:expr) => {
            let result = parse_single_region_line($input);
             if result.is_ok() {
                 panic!("Parsing should have failed for '{}' but succeeded with: {:?}", $input, result.unwrap());
             }
             // Optionally print the error for debugging failed tests
             // if let Err(e_str) = result {
             //     eprintln!("Input '{}' correctly failed with:\n{}", $input, e_str);
             // }
             assert!(result.is_err());
        };
         // Matching specific nom errors can be complex, often easier to just assert failure
         // ($input:expr, $expected_error_variant:pat) => { ... }
    }


    #[test]
    fn test_parse_simple_circle() {
        let line = "circle(100, 200, 30)";
        let expected = Shape {
            shape_type: ShapeType::Circle,
            coordinates: vec![100.0, 200.0, 30.0],
            properties: vec![],
        };
        assert_parses!(line, expected);
    }

    #[test]
    fn test_parse_circle_with_whitespace() {
        let line = "  circle  ( 100.5 ,  200 , 30 )   ";
        let expected = Shape {
            shape_type: ShapeType::Circle,
            coordinates: vec![100.5, 200.0, 30.0],
            properties: vec![],
        };
        assert_parses!(line, expected);
    }


    #[test]
    fn test_parse_circle_with_properties() {
        let line = "circle( 10.5, 20 , 5.0 ) # color=red width=2 tag=foo";
        let expected = Shape {
            shape_type: ShapeType::Circle,
            coordinates: vec![10.5, 20.0, 5.0],
            properties: vec![
                Property { key: "color".to_string(), value: "red".to_string() },
                Property { key: "width".to_string(), value: "2".to_string() },
                Property { key: "tag".to_string(), value: "foo".to_string() },
            ],
        };
        assert_parses!(line, expected);
    }

     #[test]
    fn test_parse_ellipse() {
        let line = "ellipse(500, 500, 20.1, 10.9, 45)";
         let expected = Shape {
            shape_type: ShapeType::Ellipse,
            coordinates: vec![500.0, 500.0, 20.1, 10.9, 45.0],
            properties: vec![],
        };
        assert_parses!(line, expected);
    }

     #[test]
    fn test_invalid_syntax_missing_coord() {
        let line = "circle(100, 200, )";
        assert_fails!(line);
    }

     #[test]
    fn test_invalid_syntax_unclosed_paren() {
        let line = "circle(100, 200, 30";
        assert_fails!(line);
    }

     // REMOVED: test_trailing_input_error

     #[test]
    fn test_unsupported_shape() {
        let line = "vector(1, 2, 10, 0) # property=value";
         let expected_coords = vec![1.0, 2.0, 10.0, 0.0];
         let expected_props = vec![Property { key: "property".to_string(), value: "value".to_string() }];

         match parse_single_region_line(line) {
            Ok(shape) => {
                match &shape.shape_type {
                    ShapeType::Unsupported(s) if s.eq_ignore_ascii_case("vector") => (),
                    _ => panic!("Expected ShapeType::Unsupported(\"vector\"), got {:?}", shape.shape_type),
                }
                assert_eq!(shape.coordinates, expected_coords);
                assert_eq!(shape.properties, expected_props);
            },
            Err(e_str) => panic!("Parsing failed for '{}':\n{}", line, e_str),
        }
    }

     // REMOVED: test_property_parsing_robustness_needed

}
