# Rusty Region: A DS9 Region File Parser in Rust (with Python Bindings)

`rusty_region` is a Rust library aimed at parsing DS9 region files, a common format in astronomy for defining regions of interest in images and sky coordinates. This project also provides Python bindings, allowing the Rust parser to be used from Python.

**Current Status: Work In Progress & Experimental**

❗ **IMPORTANT NOTE:** This project is currently under active development and should be considered **experimental**. The parser is not yet complete and may not correctly handle all valid DS9 region file syntax or semantics. It is **not yet recommended for production use** or for parsing critical data where accuracy is paramount.

Key features are still being implemented, and the API (both Rust and Python) is subject to change.

## Features (Planned & In Progress)

* Parsing of basic region shapes (circle, ellipse, box, polygon, point, line).
* Extraction of shape coordinates (currently parsed as `f64` values).
* Parsing of associated properties/tags.
* Python bindings via PyO3 for easy integration.
* Semantic understanding of coordinate types (CoordOdd, CoordEven, Distance, Angle, Integer) and shape-specific coordinate counts.
* Parsing of sexagesimal coordinates (e.g., `10h20m30.5s`, `+15d30m45s`).
* Handling of coordinate units (e.g., `d`, `'`, `"`, `h`, `m`, `s`, `px`).

## Current Limitations

* **Coordinate Parsing:**
    * Currently, all numeric coordinate values are parsed as simple `f64` floating-point numbers.
    * While the structure for semantic coordinate types (CoordOdd, CoordEven, etc.) and parsing different formats (sexagesimal with units, colon-separated) is being implemented, the conversion to a final, consistent decimal degree value (or other canonical form) is still basic. For instance, `10h20m30s` might be parsed and scaled, but the full sexagesimal logic is a work in progress.
    * Unit handling for `Distance` types (e.g., converting arcseconds or arcminutes to degrees) is not yet fully implemented. Values are parsed, but scaling based on units like `"` or `'` is a TODO.
* **Property Value Parsing:** The parser for property values (e.g., `text={some text with spaces}`) is currently simplified and may not correctly handle values containing spaces unless they are quoted or bracketed (and even then, advanced quoting/escaping is not yet supported).
* **Shape-Specific Coordinate Validation:** While the parser now has definitions for expected coordinate counts for various shapes, the semantic validation (e.g., ensuring a `Distance` parameter has appropriate units for the current coordinate system) is not yet implemented.
* **Global Keywords & Coordinate Systems:** Parsing and handling of global keywords (e.g., `fk5`, `icrs`, `image`, `global color=green`) are not yet implemented. The parser currently assumes a generic context for coordinates.
* **Error Reporting:** Error messages from `nom` are used, and while `VerboseError` provides some detail, more user-friendly and context-specific error reporting is planned.
* **Completeness:** Not all DS9 region shapes or their more complex features are supported yet.

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

Once built and installed, you can import and use the parser in Python:

```python
import rusty_region_parser # Or the name specified in your pyproject.toml

line = "circle(100.5, 201.2, 30.0) # color=red text={My Circle}"

try:
    shape = rusty_region_parser.parse_region_line(line)
    print(f"Shape Type: {shape.shape_type_str}")
    print(f"Coordinates: {shape.coordinates}")
    if shape.properties:
        print("Properties:")
        for prop in shape.properties:
            print(f"  - {prop.key}: {prop.value}")
    else:
        print("No properties.")

except ValueError as e:
    print(f"Error parsing region line: {e}")

# Example with an invalid line for testing error handling
invalid_line = "circle(100,200)" # Missing radius, should fail validation
try:
    shape_invalid = rusty_region_parser.parse_region_line(invalid_line)
    print(f"Parsed invalid shape (unexpected success): {shape_invalid.shape_type_str}")
except ValueError as e:
    print(f"\nCorrectly failed to parse invalid line: {e}")
```

## Contributing

Contributions are welcome, especially as this project is in its early stages! Please feel free to open issues for bugs or feature requests, or submit pull requests.

## Future Work

* Implement full parsing and conversion for all sexagesimal coordinate formats (HMS, DMS).
* Implement comprehensive unit parsing and conversion for Distance and Angle types.
* Complete semantic validation of coordinates based on ShapeSignature and the active coordinate system.
* Parse and handle global keywords and coordinate system context (e.g., fk5, image, wcs).
* Support for all standard DS9 region shapes and their variations.
* More robust parsing of property values, including quoted and bracketed text with escaped characters.
* Improved error reporting with more specific and user-friendly messages.
* Add support for parsing entire region files, not just single lines.
* Expand Python API for more detailed interaction with parsed components.

## License

This project is licensed under the MIT License. See the LICENSE file for details (if one is created).
