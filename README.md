# Rusty Region: A DS9 Region File Parser in Rust (with Python Bindings)

`rusty_region` is a Rust library aimed at parsing DS9 region files, a common format in astronomy for defining regions of interest in images and sky coordinates. This project uses the `nom` parser combinator library and provides Python bindings via `PyO3`.

**Current Status: Work In Progress & Experimental**

❗ **IMPORTANT NOTE:** This project is currently under active development and should be considered **experimental**. The parser is not yet complete and may not correctly handle all valid DS9 region file syntax or semantics. It is **not yet recommended for production use** or for parsing critical data where accuracy is paramount.

Key features are still being implemented, and the API (both Rust and Python) is subject to change.

## Features

* Parsing of basic region shapes (e.g., circle, ellipse, box, polygon, point, line).
* Extraction of shape coordinates (currently parsed as `f64` values).
* Parsing of associated properties/tags (e.g., `# color=red text={some text}`).
* Handling of **coordinate system commands** (e.g., `fk5;`, `image`). A line can contain only the command, or the command followed by a shape.
* Parsing of **exclusion regions** (e.g., `-circle(1,2,3)`).
* Initial implementation of **shape signatures** to validate the *number* of coordinates for known shapes based on semantic types (CoordOdd, CoordEven, Distance, Angle, Integer).
* Python bindings via PyO3 for easy integration.

## Current Limitations

* **Coordinate Value Parsing:**
    * Currently, all numeric coordinate values are parsed as simple `f64` floating-point numbers by the semantic parsers (`parse_coord_odd`, `parse_distance`, etc.).
    * Full parsing and conversion for sexagesimal coordinates (e.g., `10h20m30.5s`, `+15d30m45s`) and values with units (e.g., `10"`, `5d`, `2.5r`) is **not yet fully implemented** within these semantic parsers. While the structure for different formats is present, the detailed conversion logic (e.g., HMS to decimal degrees, scaling arcseconds to degrees) is a primary TODO.
* **Property Value Parsing:** The parser for property values (e.g., `text={some text with spaces}`) is currently simplified and may not correctly handle values containing spaces unless they are quoted or bracketed (and even then, advanced quoting/escaping is not yet supported).
* **Semantic Coordinate Type Validation:** While shape signatures define expected semantic types for coordinates, the individual semantic parsers (`parse_coord_odd`, etc.) currently only enforce that a parsable `f64` is present. They do not yet validate if the *format* of that `f64` (e.g., sexagesimal for `CoordOdd`) or its associated units (if any were parsed) match the semantic expectation. This is a planned enhancement.
* **Global Keywords:** Parsing and handling of global keywords that affect multiple regions (e.g., `global color=green`) are not yet implemented beyond the initial coordinate system command.
* **Error Reporting:** Error messages from `nom` are used. While `VerboseError` provides some detail, more user-friendly and context-specific error reporting is planned.
* **Completeness:** Not all DS9 region shapes or their most complex features/variations are supported or fully validated yet. The list of shape signatures in `get_shape_signature` needs to be comprehensive.

## Building the Python Extension

This project uses `maturin` to build the Python extension module.

1.  **Install Rust:** If you haven't already, [install Rust](https://www.rust-lang.org/tools/install).
2.  **Install Maturin:**
    ```bash
    pip install maturin
    ```
3.  **Build and Install for Development:**
    Navigate to the project's root directory (where `Cargo.toml` and `pyproject.toml` are located) and run:
    ```bash
    maturin develop
    ```
    This will compile the Rust code and install the Python package into your current Python environment.

    To build a wheel for distribution:
    ```bash
    maturin build --release
    # The wheel will be in target/wheels/
    pip install target/wheels/*.whl
    ```

## Using from Python

Once built and installed, you can import and use the parser in Python. The `parse_region_line` function now returns a tuple: `(optional_coord_system_string, optional_shape_object)`.

```python
import rusty_region_parser # Or the name specified in your pyproject.toml

lines_to_test = [
    "fk5; circle(100, 200, 30) # color=red",
    "IMAGE", 
    "-box(10,20,5,3,0)",
    "polygon(1,2,3,4,5,6,7,8) # text={A Polygon}"
]

for i, line_str in enumerate(lines_to_test):
    print(f"\n--- Parsing: \"{line_str}\" ---")
    try:
        # parse_region_line now returns a tuple: (coord_system_str_opt, shape_opt)
        coord_system, shape = rusty_region_parser.parse_region_line(line_str)
        
        if coord_system:
            print(f"Coordinate System: {coord_system}")
        else:
            print("Coordinate System: Not specified (or default)")

        if shape:
            print(f"Shape Type: {shape.shape_type_str}")
            print(f"Exclude: {shape.exclude}")
            print(f"Coordinates: {shape.coordinates}")
            if shape.properties:
                print("Properties:")
                for prop in shape.properties:
                    print(f"  - {prop.key}: {prop.value}")
            else:
                print("No properties.")
        else:
            print("No shape parsed on this line.")

    except ValueError as e:
        print(f"Error parsing region line: {e}")
```

## Future Work

* Implement full parsing and conversion for all sexagesimal coordinate formats (HMS, DMS) within the semantic parsers.
* Implement comprehensive unit parsing and conversion for `Distance` and `Angle` types (e.g., convert arcseconds, arcminutes, radians to a canonical unit like degrees).
* Complete semantic validation of coordinate *values* (not just counts) based on `ShapeSignature` and the active coordinate system.
* Parse and handle global keywords that affect multiple regions (e.g., `global color=green`, `wcs`, etc.).
* Support for all standard DS9 region shapes and their variations with accurate signatures.
* More robust parsing of property values, including quoted and bracketed text with escaped characters.
* Improved error reporting with more specific and user-friendly messages.
* Add support for parsing entire region files (multiple lines, comments, includes), not just single lines.
* Expand Python API for more detailed interaction with parsed components (e.g., richer coordinate objects).