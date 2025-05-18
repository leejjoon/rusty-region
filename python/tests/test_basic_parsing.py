import pytest
import numpy as np
from rusty_region import parse_region_string
from rusty_region.region import FormatType


def test_parse_simple_circle():
    """Test parsing a simple circle region"""
    region_string = "circle(100, 100, 20)"
    region = parse_region_string(region_string)
    
    # Check that we have one shape
    assert len(region) == 1
    
    # Get the shape
    shape = region[0]
    
    # Check shape properties
    assert shape.shape_type == "circle"
    assert len(shape.coordinates) == 3  # x, y, radius
    assert shape.coordinates[0] == 100.0
    assert shape.coordinates[1] == 100.0
    assert shape.coordinates[2] == 20.0


def test_parse_multiline_region():
    """Test parsing a multi-line region string"""
    region_string = """# Region file format: DS9 version 4.1
circle(100, 100, 20)
circle(200, 200, 30)"""
    
    region = parse_region_string(region_string)
    
    # We should have two shapes
    assert len(region) == 2
    
    # First shape should be a circle
    assert region[0].shape_type == "circle"
    
    # Second shape should be a circle
    assert region[1].shape_type == "circle"
