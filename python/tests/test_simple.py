import pytest
from rusty_region import parse_region_string


def test_simple_circle():
    """Test parsing a simple circle region"""
    # Create a simple region string
    region_string = "circle(100, 100, 20)"
    
    # Parse the region string
    region = parse_region_string(region_string)
    
    # Print debug information
    print(f"Region: {region}")
    print(f"Number of shapes: {len(region)}")
    if len(region) > 0:
        print(f"First shape: {region[0]}")
    
    # Basic assertions
    assert len(region) > 0, "Region should contain at least one shape"
