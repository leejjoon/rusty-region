# Rusty Region Installation Guide

This document provides comprehensive installation instructions for the Rusty Region project, which consists of a Rust library for parsing DS9 region files and a Python wrapper for easier integration with Python workflows.

## Project Structure

The project has two main components:

1. **Rust Library**: The core parser implemented in Rust with PyO3 bindings
2. **Python Wrapper**: A high-level Python API that wraps the Rust library

## Installing the Rust Library

### Prerequisites

- Rust (latest stable version)
- Cargo (comes with Rust)

### Installation Steps

1. Clone the repository:

```bash
git clone https://github.com/leejjoon/rusty-region.git
cd rusty-region
```

2. Build the library:

```bash
cargo build --release
```

3. Run the tests to verify everything works:

```bash
cargo test
```

## Installing the Python Wrapper

For detailed Python wrapper installation instructions, see [python/INSTALL.md](python/INSTALL.md).

### Quick Start

1. Install the Python package with a single command:

```bash
cd python
pip install -e .
```

This command will:
- Build the Rust extension module (`rusty_region_parser`) automatically
- Install the Python wrapper package (`rusty_region`)
- Use a modern `pyproject.toml` file for configuration

No separate Rust build step is needed - Maturin handles the integration automatically. Maturin is specifically designed for Rust-Python integration and ensures that the Rust extension is properly built and installed.

3. Verify the installation:

```python
import rusty_region
print(rusty_region.__version__)
```

## Using as a Rust Library

If you want to use Rusty Region as a dependency in another Rust project, add it to your `Cargo.toml`:

```toml
[dependencies]
rusty_region = { git = "https://github.com/leejjoon/rusty-region.git" }
```

Then you can use it in your Rust code:

```rust
use rusty_region::parse_region_file;

fn main() {
    let region = parse_region_file("path/to/region.reg").unwrap();
    // Use the region...
}
```

## Development Setup

If you want to contribute to the project, follow these steps for a development setup:

### Rust Development

1. Clone the repository:

```bash
git clone https://github.com/leejjoon/rusty-region.git
cd rusty-region
```

2. Build in debug mode for faster compilation during development:

```bash
cargo build
```

3. Run tests:

```bash
cargo test
```

### Python Development

1. Install the Python package in development mode:

```bash
cd python
pip install -e .
```

2. Run the example script:

```bash
python examples/basic_usage.py
```

## Troubleshooting

### Common Issues

#### PyO3 Compilation Errors

If you encounter errors related to PyO3, make sure you have the Python development headers installed:

- On Ubuntu/Debian: `sudo apt-get install python3-dev`
- On Fedora: `sudo dnf install python3-devel`
- On macOS with Homebrew: `brew install python`

#### Rust Version Issues

This project requires Rust 1.48 or later due to PyO3 requirements. Update your Rust installation if needed:

```bash
rustup update
```

#### Python Import Errors

If you get import errors when trying to use the Python package, make sure:

1. The Rust library built successfully
2. The Python package is installed correctly
3. You're using the same Python interpreter for installation and running

## Getting Help

If you continue to experience issues, please open an issue on the GitHub repository with details about your system and the error messages you're seeing.
