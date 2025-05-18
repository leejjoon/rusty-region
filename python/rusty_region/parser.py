# parser.py - Functions for parsing region files and strings

from typing import List, Dict, Union, Optional, Tuple, Any
import os
from pathlib import Path

from .rusty_region_parser import parse_region_line as rust_parse_region_line
from .region import Region, Shape


def parse_region_string(region_string: str) -> Region:
    """Parse a region string into a Region object
    
    Args:
        region_string: String containing region definitions
        
    Returns:
        Region object containing parsed shapes and properties
    """
    region = Region()
    active_coord_system = None
    
    for line in region_string.splitlines():
        if not line.strip():
            continue
            
        # Parse the line using the Rust parser
        try:
            result = rust_parse_region_line(line, active_coord_system)
            
            # Unpack the result tuple: (coord_system, shape_obj, global_attrs, comment, new_active_system)
            # Note: The order is different from what we expected before
            coord_system, shape_obj, global_attrs, comment, new_active_system = result
            
            # Debug output
            print(f"Parsed line: '{line}'")
            print(f"  coord_system: {coord_system}")
            print(f"  shape_obj: {shape_obj}")
            print(f"  global_attrs: {global_attrs}")
            print(f"  comment: {comment}")
            print(f"  new_active_system: {new_active_system}")
            
        except Exception as e:
            # Skip lines that can't be parsed
            print(f"Warning: Failed to parse line: '{line}'. Error: {e}")
            continue
        
        # Update the active coordinate system if a new one was specified
        if new_active_system is not None:
            active_coord_system = new_active_system
        
        # Handle different types of lines
        if shape_obj is not None:
            # Create a Shape object and add it to the region
            print(f"  Adding shape: {shape_obj}")
            region.add_shape(Shape(shape_obj))
        if global_attrs is not None:
            # Update global properties
            print(f"  Adding global attributes: {global_attrs}")
            region.update_global_properties(global_attrs)
        if comment is not None:
            # Add a comment
            print(f"  Adding comment: {comment}")
            region.add_comment(comment)
    
    return region


def parse_region_file(file_path: Union[str, Path]) -> Region:
    """Parse a region file into a Region object
    
    Args:
        file_path: Path to the region file
        
    Returns:
        Region object containing parsed shapes and properties
        
    Raises:
        FileNotFoundError: If the file doesn't exist
    """
    file_path = Path(file_path)
    if not file_path.exists():
        raise FileNotFoundError(f"Region file not found: {file_path}")
    
    with open(file_path, 'r') as f:
        region_string = f.read()
    
    return parse_region_string(region_string)
