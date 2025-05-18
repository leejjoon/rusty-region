# Installation Guide for Rusty Region

This document provides instructions for installing the `rusty_region` Python package, which is a wrapper around the Rust-based DS9 region file parser.

## Prerequisites

Before installing `rusty_region`, you need to have the following installed:

- Python 3.6 or later
- Rust (latest stable version recommended)
- Cargo (comes with Rust)
- A C compiler (for building the Rust extension)

### Installing Rust

If you don't have Rust installed, you can install it using rustup:

```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

On Windows, download and run [rustup-init.exe](https://win.rustup.rs/) from the official website.

After installation, make sure Rust is in your PATH by running:

```bash
rustc --version
cargo --version
```

## Installation Methods

### Method 1: Install from PyPI (for users)

Once the package is published to PyPI, you can install it with pip:

```bash
pip install rusty_region
```

This will automatically download and build the Rust extension.

### Method 2: Install from Source (for developers)

1. Clone the repository:

```bash
git clone https://github.com/leejjoon/rusty-region.git
cd rusty-region
```

2. Install the Python package in development mode:

```bash
cd python
pip install -e .
```

This command will:
- Build the Rust extension module (`rusty_region_parser`) using Maturin
- Install the Python wrapper package (`rusty_region`)
- Use the `pyproject.toml` file for configuration (the modern approach for Python packaging)

The integration between the Rust extension and Python package is handled automatically by Maturin, which is specifically designed for Rust-Python integration.

This will install the package in "editable" mode, meaning changes to the Python code will be immediately available without reinstalling.

## Verifying Installation

To verify that the installation was successful, run Python and try importing the package:

```python
import rusty_region
print(rusty_region.__version__)
```

You can also run one of the example scripts:

```bash
python examples/basic_usage.py
```

## Troubleshooting

### Common Issues

#### Missing Rust Compiler

If you get an error about a missing Rust compiler, make sure Rust is installed and in your PATH.

#### Build Errors

If you encounter build errors:

1. Make sure you have the latest version of Rust:
```bash
rustup update
```

2. Check that you have a C compiler installed:
   - On Linux: `gcc` or `clang`
   - On macOS: Xcode Command Line Tools
   - On Windows: Microsoft Visual C++ Build Tools

3. Try cleaning the build and rebuilding:
```bash
cargo clean
cargo build --release
```

#### Python Version Compatibility

The package requires Python 3.6 or later. If you're using an older version, you'll need to upgrade.

### Getting Help

If you continue to experience issues, please open an issue on the GitHub repository with details about your system and the error messages you're seeing.

## Dependencies

The Python package depends on:

- NumPy
- Matplotlib

These will be automatically installed when you install the package using pip.
