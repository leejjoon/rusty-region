import pytest
import os
import sys

# Add the parent directory to the path so we can import the package
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Sample region strings that can be reused across tests
@pytest.fixture
def simple_region_string():
    return "circle(100, 100, 20)"

@pytest.fixture
def region_with_properties():
    return "circle(100, 100, 20) # color=red width=2 text={Hello World}"

@pytest.fixture
def region_with_sexagesimal():
    return "fk5\ncircle(12:34:56.7, -45:12:30, 0.5')"

@pytest.fixture
def multiple_shapes_region():
    return """circle(100, 100, 20)
    box(200, 200, 30, 40)
    polygon(300, 300, 320, 320, 280, 320)"""
