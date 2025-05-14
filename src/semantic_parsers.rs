//! # Semantic Coordinate Parsers
//!
//! This module contains parsers for specific semantic coordinate types
//! (e.g., CoordOdd, Distance) as defined for DS9 regions.
//! For now, they all parse f64 values but can be enhanced later by
//! making them return richer types like a dedicated Sexagesimal struct.

use nom::{
    IResult,
    branch::alt,
    // Correctly import tag and tag_no_case
    bytes::complete::{tag, tag_no_case}, 
    character::complete::{char as nom_char, digit1, multispace0},
    combinator::{map, map_res, opt, recognize, value, verify}, 
    error::{context, ParseError as NomParseErrorTrait, VerboseError}, // Added VerboseError for tests
    number::complete::double,
    sequence::{delimited, pair, preceded, terminated, tuple},
};
use std::str::FromStr;
// Assumes these are pub(crate) or pub in lib.rs or a shared prelude module
use crate::{Input, NomVerboseError, ParserResult, SemanticCoordType, ws, CoordSystem};


// --- Helper Parsers for Numbers ---

/// Parses an optional sign (+ or -)
fn parse_optional_sign<'a>(input: Input<'a>) -> ParserResult<'a, Option<char>> {
    opt(alt((nom_char('+'), nom_char('-'))))(input)
}

/// Parses an unsigned integer string and converts to f64.
fn parse_unsigned_integer_as_f64<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    map_res(digit1, |s: Input<'a>| f64::from_str(s))(input)
}

/// Parses a potentially signed floating point number (like "123.45", "-10", "+.5").
/// This is the base for "simple number" parsing. Handles surrounding whitespace.
fn parse_simple_signed_f64_ws<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    context(
        "simple signed f64",
        preceded(ws, terminated(double, ws)) // `double` handles sign and format
    )(input)
}

/// Parses an integer (possibly signed) and returns it as f64.
/// Fails if the number has a fractional part. Handles surrounding whitespace.
fn parse_integer_value_as_f64_ws<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    context(
        "integer as f64",
        preceded(ws, terminated(
            // Use `verify` to check if the parsed double has a fractional part.
            verify(
                double, // Parse as a float first
                |val: &f64| val.fract() == 0.0 // Condition: must have no fractional part
            ),
            ws
        ))
    )(input)
}


// --- Parsers for Sexagesimal-like and Unit-based Formats ---

/// Parses HHh[MMm[SSs]] or DDd[MMm[SSs]] like formats.
/// Returns the calculated decimal value, scaled by the `scale` argument.
fn parse_sexagesimal_units_format<'a>(
    primary_unit_static_tag: &'static str,
    scale: f64, // New scale argument
    ctx_label: &'static str
) -> impl FnMut(Input<'a>) -> ParserResult<'a, f64> {
    move |i: Input<'a>| {
        context(
            ctx_label,
            map(
                tuple((
                    parse_optional_sign, // sign
                    double, // v1: HH or DD component
                    tag_no_case(primary_unit_static_tag), // h/H or d/D
                    opt(preceded(multispace0, // Optional space before minutes
                        tuple((
                            double, // v2: MM component
                            tag_no_case("m"),
                            opt(preceded(multispace0, // Optional space before seconds
                                tuple((
                                    double, // v3: SS component
                                    tag_no_case("s")
                                ))
                            ))
                        ))
                    ))
                )),
                // Calculate the decimal value: val = sign * (v1 + v2/60 + v3/3600) * scale
                |(sign_opt, v1, _unit1_tag, minutes_seconds_opt)| {
                    let mut total_value = v1;
                    if let Some((v2, _m_tag, seconds_opt)) = minutes_seconds_opt {
                        total_value += v2 / 60.0;
                        if let Some((v3, _s_tag)) = seconds_opt {
                            total_value += v3 / 3600.0;
                        }
                    }
                    let final_value = if sign_opt == Some('-') { -total_value } else { total_value };
                    final_value * scale // Apply scaling
                }
            )
        )(i)
    }
}

/// Parses V1:V2[:V3] (colon-separated sexagesimal).
/// Returns the calculated decimal value, scaled by the `scale` argument.
fn parse_colon_sexagesimal_format<'a>(
    scale: f64, // New scale argument
    ctx_label: &'static str
) -> impl FnMut(Input<'a>) -> ParserResult<'a, f64> {
    move |i: Input<'a>| {
        context(
            ctx_label,
            map(
                tuple((
                    parse_optional_sign,
                    double, // V1
                    nom_char(':'),
                    double, // V2
                    opt(preceded(nom_char(':'), double)) // Optional V3
                )),
                |(sign_opt, v1, _, v2, v3_opt)| {
                    let mut total_value = v1;
                    total_value += v2 / 60.0;
                    if let Some(v3) = v3_opt {
                        total_value += v3 / 3600.0;
                    }
                    let final_value = if sign_opt == Some('-') { -total_value } else { total_value };
                    final_value * scale // Apply scaling
                }
            )
        )(i)
    }
}

/// Parses a value with an angular unit (d, ', ", r).
/// Returns the numerical value converted to degrees.
fn parse_angular_distance_units_format<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    context(
        "angular distance with unit",
        map(
            pair(
                double, // The numerical value
                alt((
                    tag_no_case("d"),
                    tag_no_case("r"), // radians
                    tag("\""), // arcseconds (double quote)
                    tag("'"),  // arcminutes (single quote)
                ))
            ),
            |(val, unit_tag): (f64, &str)| {
                if unit_tag.eq_ignore_ascii_case("d") {
                    val
                } else if unit_tag.eq_ignore_ascii_case("r") {
                    val.to_degrees() // Convert radians to degrees
                } else if unit_tag == "'" {
                    val / 60.0 // Convert arcminutes to degrees
                } else if unit_tag == "\"" {
                    val / 3600.0 // Convert arcseconds to degrees
                } else {
                    val // Should not happen with the alt above, but as a fallback
                }
            }
        )
    )(input)
}


// --- Semantic Coordinate Parsers ---

pub(crate) fn parse_coord_odd<'a>(active_system: Option<&CoordSystem>, input: Input<'a>) -> ParserResult<'a, f64> {
    let scale_for_colon_ra = match active_system {
        Some(CoordSystem::Physical) | Some(CoordSystem::Image) | Some(CoordSystem::Linear) |
        Some(CoordSystem::Detector) | Some(CoordSystem::Amplifier) | Some(CoordSystem::Unknown(_)) => 1.0,
        _ => 15.0, // Default to celestial (hours -> degrees) for FK5, J2000, ICRS, Galactic, Ecliptic, or None
    };
    context(
        "CoordOdd (RA-like)",
        preceded(ws, // Consume leading whitespace for the whole CoordOdd
            terminated( // Consume trailing whitespace after the chosen format
                alt((
                    parse_sexagesimal_units_format("h", 15.0, "HMS format (e.g., 10h20m30s)"),
                    parse_colon_sexagesimal_format(scale_for_colon_ra, "Colon-separated HMS"),
                    double // Fallback to simple double (assumed to be degrees already)
                )),
                ws
            )
        )
    )(input)
}

pub(crate) fn parse_coord_even<'a>(active_system: Option<&CoordSystem>, input: Input<'a>) -> ParserResult<'a, f64> {
    // For Dec, colon format is generally always degrees.
    let scale_for_colon_dec = 1.0;
    context(
        "CoordEven (Dec-like)",
        preceded(ws,
            terminated(
                alt((
                    parse_sexagesimal_units_format("d", 1.0, "DMS format (e.g., +10d20m30s)"),
                    parse_colon_sexagesimal_format(scale_for_colon_dec, "Colon-separated DMS"),
                    double // Fallback to simple double (assumed to be degrees already)
                )),
                ws
            )
        )
    )(input)
}

pub(crate) fn parse_distance<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    context(
        "Distance (angular size)",
        preceded(ws,
            terminated(
                alt((
                    parse_angular_distance_units_format, 
                    double 
                )),
                ws
            )
        )
    )(input)
}

pub(crate) fn parse_angle<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    parse_simple_signed_f64_ws(input)
}

pub(crate) fn parse_integer_as_f64<'a>(input: Input<'a>) -> ParserResult<'a, f64> {
    parse_integer_value_as_f64_ws(input)
}

/// Dispatches to the correct semantic parser, passing the active coordinate system.
pub(crate) fn dispatch_semantic_parser<'a>(
    semantic_type: SemanticCoordType,
    active_system: Option<&'a CoordSystem>, // Accept active_system
) -> impl FnMut(Input<'a>) -> ParserResult<'a, f64> + 'a { // Ensure lifetime 'a is part of the closure
    move |i: Input<'a>| { // The input 'i' also has lifetime 'a
        match semantic_type {
            SemanticCoordType::CoordOdd => parse_coord_odd(active_system, i),
            SemanticCoordType::CoordEven => parse_coord_even(active_system, i),
            SemanticCoordType::Distance => parse_distance(i), 
            SemanticCoordType::Angle => parse_angle(i),
            SemanticCoordType::Integer => parse_integer_as_f64(i),
        }
    }
}

// --- Unit Tests ---
#[cfg(test)]
mod tests {
    use super::*;
    use nom::Finish; 

    macro_rules! assert_parser_ok {
        ($parser:expr, $input:expr, $expected_output:expr, $expected_remaining:expr) => {
            match $parser($input) {
                Ok((remaining, output)) => {
                    assert_eq!(remaining, $expected_remaining, "Remaining input mismatch for '{}'", $input);
                    assert!((output - $expected_output).abs() < 1e-9, "Parsed value mismatch for '{}': got {}, expected {}", $input, output, $expected_output);
                }
                Err(e) => {
                    let e_str = match e {
                        nom::Err::Error(ve) | nom::Err::Failure(ve) => nom::error::convert_error($input, ve),
                        nom::Err::Incomplete(_) => "Incomplete".to_string(),
                    };
                    panic!("Parser failed for input '{}': {:?}", $input, e_str)
                },
            }
        };
    }

    macro_rules! assert_parser_err {
        ($parser:expr, $input:expr) => {
            assert!($parser($input).is_err(), "Parser should have failed for input '{}'", $input);
        };
    }

    #[test]
    fn test_parse_simple_signed_f64_ws_valid() {
        assert_parser_ok!(parse_simple_signed_f64_ws, " 123.45 ", 123.45, "");
        assert_parser_ok!(parse_simple_signed_f64_ws, "-10", -10.0, "");
    }

    #[test]
    fn test_parse_integer_value_as_f64_ws_valid() {
        assert_parser_ok!(parse_integer_value_as_f64_ws, " 123 ", 123.0, "");
        assert_parser_ok!(parse_integer_value_as_f64_ws, "-10", -10.0, "");
        assert_parser_ok!(parse_integer_value_as_f64_ws, "123.0", 123.0, ""); 
    }

    #[test]
    fn test_parse_integer_value_as_f64_ws_invalid_fractional() {
        assert_parser_err!(parse_integer_value_as_f64_ws, " 12.3 "); 
    }

    #[test]
    fn test_parse_sexagesimal_units_format_hms_scaled() {
        let mut parser = parse_sexagesimal_units_format("h", 15.0, "HMS scaled test");
        assert_parser_ok!(parser, "1h", 1.0 * 15.0, "");
        assert_parser_ok!(parser, "-2h30m", -(2.0 + 30.0/60.0) * 15.0, ""); 
        assert_parser_ok!(parser, "+1h0m36s", (1.0 + 36.0/3600.0) * 15.0, ""); 
    }

    #[test]
    fn test_parse_sexagesimal_units_format_dms_no_scale() {
        let mut parser = parse_sexagesimal_units_format("d", 1.0, "DMS no scale test");
        assert_parser_ok!(parser, "150d", 150.0, "");
        assert_parser_ok!(parser, "-10d30m", -(10.0 + 30.0/60.0), "");
    }
    
    #[test]
    fn test_parse_colon_sexagesimal_format_scaled() {
        let mut parser = parse_colon_sexagesimal_format(15.0, "Colon HMS scaled");
        assert_parser_ok!(parser, "2:00:00", (2.0) * 15.0, "");
        assert_parser_ok!(parser, "01:30:00", (1.0 + 30.0/60.0) * 15.0, "");
    }

    #[test]
    fn test_parse_colon_sexagesimal_format_no_scale() {
        let mut parser = parse_colon_sexagesimal_format(1.0, "Colon DMS no scale");
        assert_parser_ok!(parser, "10:30", 10.0 + 30.0/60.0, "");
        assert_parser_ok!(parser, "-5:15:36", -(5.0 + 15.0/60.0 + 36.0/3600.0), "");
    }

    #[test]
    fn test_parse_angular_distance_units_format_valid_degrees() {
        assert_parser_ok!(parse_angular_distance_units_format, "10d", 10.0, "");
        assert_parser_ok!(parse_angular_distance_units_format, "20.5'", 20.5 / 60.0, "");
        assert_parser_ok!(parse_angular_distance_units_format, "30\"", 30.0 / 3600.0, "");
        assert_parser_ok!(parse_angular_distance_units_format, "1.5r", 1.5_f64.to_degrees(), "");
        assert_parser_ok!(parse_angular_distance_units_format, "1R", 1.0_f64.to_degrees(), ""); 
    }

    #[test]
    fn test_parse_coord_odd_celestial_context() {
        assert_parser_ok!(|i| parse_coord_odd(None, i), " 1:0:0 ", 15.0, "");
        assert_parser_ok!(|i| parse_coord_odd(Some(&CoordSystem::Fk5), i), " 1:0:0 ", 15.0, "");
        assert_parser_ok!(|i| parse_coord_odd(Some(&CoordSystem::Image), i), "1h", 15.0, "");
    }

    #[test]
    fn test_parse_coord_odd_physical_context() {
        assert_parser_ok!(|i| parse_coord_odd(Some(&CoordSystem::Image), i), " 10.5 ", 10.5, "");
        assert_parser_ok!(|i| parse_coord_odd(Some(&CoordSystem::Physical), i), " 10:30 ", 10.5, ""); 
    }


    #[test]
    fn test_parse_coord_even_celestial_context() {
        assert_parser_ok!(|i| parse_coord_even(None, i), " 10:30:0 ", 10.5, "");
        assert_parser_ok!(|i| parse_coord_even(Some(&CoordSystem::Fk5), i), " 10:30:0 ", 10.5, "");
        assert_parser_ok!(|i| parse_coord_even(Some(&CoordSystem::Image), i), "10d", 10.0, "");

    }
    
    #[test]
    fn test_parse_coord_even_physical_context() {
        assert_parser_ok!(|i| parse_coord_even(Some(&CoordSystem::Image), i), " 10.5 ", 10.5, "");
        assert_parser_ok!(|i| parse_coord_even(Some(&CoordSystem::Physical), i), " 10:30 ", 10.5, "");
    }


    #[test]
    fn test_parse_distance_expects_degrees() {
        assert_parser_ok!(parse_distance, " 10.5d ", 10.5, "");
        assert_parser_ok!(parse_distance, " 30\" ", 30.0 / 3600.0, ""); 
        assert_parser_ok!(parse_distance, " 60' ", 1.0, ""); 
        assert_parser_ok!(parse_distance, " 200.0 ", 200.0, ""); 
    }

    #[test]
    fn test_parse_angle() {
        assert_parser_ok!(parse_angle, " 90 ", 90.0, "");
        assert_parser_ok!(parse_angle, " -45.5 ", -45.5, "");
    }

    #[test]
    fn test_parse_integer_as_f64() {
        assert_parser_ok!(parse_integer_as_f64, " 5 ", 5.0, "");
        assert_parser_ok!(parse_integer_as_f64, "-100", -100.0, "");
        assert_parser_ok!(parse_integer_as_f64, "123.0", 123.0, ""); 
        assert_parser_err!(parse_integer_as_f64, "5.5"); 
    }
}

