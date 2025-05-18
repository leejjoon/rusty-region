# rusty_region: Python wrapper for the Rust-based DS9 region file parser

# Import the Rust extension module
try:
    # Import from the local submodule (as built by Maturin)
    from .rusty_region_parser import *
except ImportError:
    raise ImportError(
        "Could not import the 'rusty_region_parser' module. "
        "Make sure the Rust extension is properly built and installed. "
        "See the installation instructions for details."
    )

# Import the high-level Python wrapper classes and functions
from .region import Region, Shape
from .parser import parse_region_file, parse_region_string

__version__ = "0.1.0"
