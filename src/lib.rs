//! # Rusty Region
//!
//! A parser for DS9 region files, written in Rust.
//! This library provides tools to parse region file strings into structured data.

// --- Module Imports ---
use winnow::prelude::*;
use winnow::token::{take_while, take_until};
use winnow::combinator::{opt, preceded, terminated, separated_pair, separated};
use winnow::ascii::{float, multispace0, multispace1, alphanumeric1};
use winnow::error::{ParserError as WinnowParserError, ErrorKind, AddContext as WinnowAddContext};
use winnow::stream::Stream; // Import Stream trait for bounds and methods like `checkpoint`

// --- Custom Error Type ---
// Input type I needs to be bound by Stream + Clone
#[derive(Debug, Clone, PartialEq)]
pub enum ParseError<I> {
    Winnow(I, ErrorKind),
    Context(I, &'static str, Box<Self>),
    Custom(I, String),
    Incomplete(I, String),
}

// Implement winnow::error::ParserError for our custom error type
// Add the `Stream` trait bound for `I`
impl<I: Stream + Clone> WinnowParserError<I> for ParseError<I> {
    fn from_error_kind(input: &I, kind: ErrorKind) -> Self {
        ParseError::Winnow(input.clone(), kind)
    }

    // The signature requires a checkpoint, which marks a position in the input stream
    fn append(self, input: &I, _checkpoint: &<I as Stream>::Checkpoint, kind: ErrorKind) -> Self {
        // Append new error info. This implementation simply replaces the old Winnow error.
        match self {
            ParseError::Winnow(_, _) => ParseError::Winnow(input.clone(), kind),
            ParseError::Context(i, ctx, inner) => ParseError::Context(i, ctx, Box::new(inner.append(input, _checkpoint, kind))),
            _ => ParseError::Winnow(input.clone(), kind),
        }
    }
}

// Implement winnow::error::AddContext for our custom error type
// Add the `Stream` trait bound for `I`
impl<I: Stream + Clone> WinnowAddContext<I, &'static str> for ParseError<I> {
     // Signature requires input, checkpoint, and context
     fn add_context(self, input: &I, _checkpoint: &<I as Stream>::Checkpoint, ctx: &'static str) -> Self {
          ParseError::Context(input.clone(), ctx, Box::new(self))
     }
}

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
// Define a type alias for the result type using PResult and our custom error
// Note: The Input type `&'a str` implements Stream + Clone implicitly.
type PResult<'a, O> = winnow::PResult<O, ParseError<Input<'a>>>;

// --- Basic Parsers ---

/// Parses zero or more whitespace characters. Returns PResult<()>
fn ws<'a>(input: &mut Input<'a>) -> PResult<'a, ()> {
    multispace0.void().parse_next(input)
}

/// Parses one or more whitespace characters. Returns PResult<()>
fn ws1<'a>(input: &mut Input<'a>) -> PResult<'a, ()> {
    multispace1.void().parse_next(input)
}


/// Parses a floating point number (f64), consuming surrounding whitespace. Returns PResult<f64>
fn parse_f64<'a>(input: &mut Input<'a>) -> PResult<'a, f64> {
    // Use function combinators `preceded` and `terminated` correctly
    terminated(
        preceded(ws, float), // Parse float after leading whitespace
        ws                   // Consume trailing whitespace
    )
    .context("floating point number")
    .parse_next(input)
}

/// Parses an identifier (alphanumeric string, e.g., shape names, property keys). Returns PResult<&str>
fn parse_identifier<'a>(input: &mut Input<'a>) -> PResult<'a, &'a str> {
    // Use function combinators `preceded` and `terminated` correctly
    terminated(
        preceded(ws, alphanumeric1), // Parse identifier after leading whitespace
        ws                           // Consume trailing whitespace
    )
    .context("identifier (letters/numbers)")
    .parse_next(input)
}


// --- Component Parsers ---

/// Parses a list of coordinates enclosed in parentheses: `( N, N, N, ... )`. Returns PResult<Vec<f64>>
fn parse_coordinates<'a>(input: &mut Input<'a>) -> PResult<'a, Vec<f64>> {
    preceded(
        (ws, '(').context("opening parenthesis for coordinates"),
        terminated(
            // `separated` with a range (1..) implicitly collects into Vec
            separated(1.., parse_f64, (ws, ',', ws))
                 // REMOVED .collect::<Vec<_>>() - `separated` handles collection
                 .context("comma-separated coordinates list"),
            (ws, ')').context("closing parenthesis for coordinates")
        )
    )
    .context("coordinate list in parentheses")
    .parse_next(input)
}

/// Parses a property value. Returns PResult<&str>
/// This is still a simplified version.
fn parse_property_value<'a>(input: &mut Input<'a>) -> PResult<'a, &'a str> {
    // Basic approach: take characters until the next whitespace or '#' or end of input.
    // TODO: Enhance this parser significantly for real-world region files (quotes, braces).
    take_while(1.., |c: char| !c.is_whitespace() && c != '#')
        .context("property value (simple version)")
        .parse_next(input)
}

/// Parses a single property: `key=value`. Returns PResult<Property>
fn parse_property<'a>(input: &mut Input<'a>) -> PResult<'a, Property> {
    separated_pair(
        parse_identifier,      // The key
        (ws, '=', ws),         // The separator
        parse_property_value   // The value
    )
    .map(|(key_str, value_str)| Property {
        key: key_str.to_string(),
        value: value_str.to_string(),
    })
    .context("key=value property")
    .parse_next(input)
}


/// Parses the optional properties/comment part after a shape definition. Returns PResult<Vec<Property>>
/// Starts with '#', followed by optional space-separated properties.
fn parse_optional_properties<'a>(input: &mut Input<'a>) -> PResult<'a, Vec<Property>> {
    opt(
        preceded(
            (ws, '#', ws1).context("property marker '#' followed by space"),
            // `separated` with a range (0..) implicitly collects into Vec
            separated(0.., parse_property, ws1)
                // REMOVED .collect::<Vec<_>>() - `separated` handles collection
                .context("list of properties")
        )
    )
    .map(|opt_props| opt_props.unwrap_or_else(Vec::new))
    .context("optional properties section starting with #")
    .parse_next(input)
}

// --- Shape Parser ---

/// Parses a full shape definition line (e.g., "circle(10, 20, 5) # color=red"). Returns PResult<Shape>
pub fn parse_shape_definition<'a>(input: &mut Input<'a>) -> PResult<'a, Shape> {
    let shape_keyword = parse_identifier.context("shape keyword (e.g., circle, box)").parse_next(input)?;
    let coords = parse_coordinates.context("shape coordinates").parse_next(input)?;
    let props = parse_optional_properties.context("optional shape properties").parse_next(input)?;

    let shape_type = match shape_keyword.to_lowercase().as_str() {
        "circle" => ShapeType::Circle,
        "ellipse" => ShapeType::Ellipse,
        "box" => ShapeType::Box,
        "polygon" => ShapeType::Polygon,
        "point" => ShapeType::Point,
        "line" => ShapeType::Line,
        _ => ShapeType::Unsupported(shape_keyword.to_string()),
    };

    Ok(Shape {
        shape_type,
        coordinates: coords,
        properties: props,
    })
}


// --- Main Parsing Function (Example Entry Point) ---

/// Parses a single line expected to contain a region shape definition.
/// Handles leading/trailing whitespace and ensures the entire line is consumed.
pub fn parse_single_region_line(line: &str) -> Result<Shape, ParseError<Input>> {
    let mut parser = preceded(ws, parse_shape_definition);
    let original_line = line; // Keep original line ref for potential error reporting
    let mut input = line;

    match parser.parse_next(&mut input) {
        Ok(shape) => {
            // Check for remaining non-whitespace input
            // Remove the incorrect generic argument `::<_>` from `ws`
            match ws.parse_next(&mut input) {
                Ok(_) => {
                    if input.is_empty() {
                        Ok(shape)
                    } else {
                        Err(ParseError::Incomplete(input, format!("Trailing input after shape definition: '{}'", input)))
                    }
                }
                // Handle ErrMode explicitly instead of using .into()
                Err(e) => Err(match e {
                     winnow::error::ErrMode::Incomplete(_) => ParseError::Custom(input, "Parser needed more input during trailing whitespace check".to_string()),
                     winnow::error::ErrMode::Cut(err) => err, // Already our ParseError type
                     winnow::error::ErrMode::Backtrack(err) => err, // Already our ParseError type
                 })
            }
        }
        Err(e) => {
            // Convert winnow::error::ErrMode into our ParseError
             Err(match e {
                 winnow::error::ErrMode::Incomplete(_) => ParseError::Custom(original_line, "Parser needed more input".to_string()),
                 winnow::error::ErrMode::Cut(err) => err,
                 winnow::error::ErrMode::Backtrack(err) => err,
             })
        }
    }
}


// --- Unit Tests ---
#[cfg(test)]
mod tests {
    use super::*; // Import everything from the parent module (lib.rs)

    // Helper macro for cleaner tests expecting Ok result
    macro_rules! assert_parses {
        ($input:expr, $expected:expr) => {
            match parse_single_region_line($input) {
                Ok(shape) => assert_eq!(shape, $expected),
                Err(e) => panic!("Parsing failed for '{}': {:?}", $input, e),
            }
        };
    }

     // Helper macro for cleaner tests expecting Err result
    macro_rules! assert_fails {
        ($input:expr) => {
            assert!(parse_single_region_line($input).is_err(), "Parsing should have failed for '{}'", $input);
        };
         ($input:expr, $expected_error_variant:pat) => {
            let result = parse_single_region_line($input);
             assert!(result.is_err(), "Parsing should have failed for '{}'", $input);
             if let Err(e) = result {
                 // Use std::mem::discriminant for pattern matching on enums with associated data
                 // if the simple matches! macro isn't sufficient or causes issues.
                 // For now, matches! should work for top-level enum variants.
                 assert!(matches!(e, $expected_error_variant), "Expected error variant {} but got {:?}", stringify!($expected_error_variant), e);
             }
        };
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
        let line = "ellipse(500, 500, 20.1, 10.9, 45)"; // x, y, r1, r2, angle
         let expected = Shape {
            shape_type: ShapeType::Ellipse,
            coordinates: vec![500.0, 500.0, 20.1, 10.9, 45.0],
            properties: vec![],
        };
        assert_parses!(line, expected);
    }

     #[test]
    fn test_invalid_syntax_missing_coord() {
        let line = "circle(100, 200, )"; // Invalid syntax: missing coordinate
        // Expect a winnow error or context error during float parsing
        assert_fails!(line, ParseError::Winnow(_,_) | ParseError::Context(_,_,_));
    }

     #[test]
    fn test_invalid_syntax_unclosed_paren() {
        let line = "circle(100, 200, 30"; // Invalid syntax: unclosed parenthesis
        // Expect a winnow error or context error looking for ')'
         assert_fails!(line, ParseError::Winnow(_,_) | ParseError::Context(_,_,_));
    }

     #[test]
    fn test_trailing_input_error() {
        let line = "circle(100, 200, 30) unexpected text"; // Trailing text not part of properties
        assert_fails!(line, ParseError::Incomplete(_, _)); // Expect Incomplete error due to remaining input
    }


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
            Err(e) => panic!("Parsing failed for '{}': {:?}", line, e),
        }
    }

     #[test]
    fn test_property_parsing_robustness_needed() {
        let line = r#"point(10, 10) # text={This has spaces} tag="quoted value""#;
        let result = parse_single_region_line(line);

        // Expect Incomplete error because simple parser stops at the space after '{This'
        assert!(result.is_err(), "Parsing should fail or be incomplete due to simple property value parser");
        if let Err(e) = result {
             assert!(matches!(e, ParseError::Incomplete(_, _) | ParseError::Winnow(_,_) | ParseError::Context(_, _, _)),
                "Expected Incomplete or other parse error due to simple property value parser, but got {:?}", e);
             eprintln!("Note: Test `test_property_parsing_robustness_needed` correctly identified failure/limitation of simple property value parser for line: '{}'. Error: {:?}", line, e);
        } else {
             panic!("Parsing unexpectedly succeeded for line with complex property values: '{}'. Result: {:?}", line, result.unwrap());
        }
    }
}
