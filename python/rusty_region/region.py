# region.py - High-level wrapper for region objects

import numpy as np
from typing import List, Dict, Union, Optional, Tuple, Any
from enum import IntEnum

# Import the Rust bindings
from .rusty_region_parser import (
    Shape as RustShape,
    parse_region_line as rust_parse_region_line,
    FORMAT_SIMPLE, FORMAT_SEXAGESIMAL_COLON, FORMAT_SEXAGESIMAL_HMS,
    FORMAT_SEXAGESIMAL_DMS, FORMAT_WITH_UNIT
)


class FormatType(IntEnum):
    """Enum for coordinate format types with human-readable names"""
    SIMPLE = FORMAT_SIMPLE
    SEXAGESIMAL_COLON = FORMAT_SEXAGESIMAL_COLON
    SEXAGESIMAL_HMS = FORMAT_SEXAGESIMAL_HMS
    SEXAGESIMAL_DMS = FORMAT_SEXAGESIMAL_DMS
    WITH_UNIT = FORMAT_WITH_UNIT


class Shape:
    """A high-level wrapper for a region shape"""
    
    def __init__(self, rust_shape):
        """Initialize from a Rust Shape object
        
        Args:
            rust_shape: A Rust Shape object or dictionary with shape data
        """
        # Handle different types of input
        if isinstance(rust_shape, dict):
            # Create a RustShape from a dictionary
            self._rust_shape = RustShape(
                rust_shape.get('shape_type', ''),
                rust_shape.get('coordinates', []),
                rust_shape.get('coordinate_formats', None),
                rust_shape.get('properties', {}),
                rust_shape.get('tags', []),
                rust_shape.get('exclude', False)
            )
        else:
            # Assume it's a RustShape object
            self._rust_shape = rust_shape
        
    @classmethod
    def create(cls, shape_type: str, coordinates: List[float], 
               coordinate_formats: Optional[List[int]] = None,
               properties: Optional[Dict[str, Any]] = None,
               tags: Optional[List[str]] = None,
               exclude: bool = False) -> 'Shape':
        """Create a new Shape object"""
        if properties is None:
            properties = {}
        if tags is None:
            tags = []
            
        rust_shape = RustShape(shape_type, coordinates, coordinate_formats, properties, tags, exclude)
        return cls(rust_shape)
    
    @property
    def shape_type(self) -> str:
        """Get the shape type (e.g., 'circle', 'box')"""
        return self._rust_shape.get_shape_type_str()
    
    @property
    def coordinates(self) -> np.ndarray:
        """Get the coordinates as a NumPy array"""
        return np.array(self._rust_shape.get_coordinates())
    
    @property
    def coordinate_formats(self) -> List[FormatType]:
        """Get the coordinate formats"""
        return [FormatType(fmt) for fmt in self._rust_shape.get_coordinate_formats()]
    
    @property
    def properties(self) -> Dict[str, Any]:
        """Get the properties dictionary"""
        return self._rust_shape.properties()
    
    @property
    def tags(self) -> List[str]:
        """Get the tags list"""
        return self._rust_shape.tags()
    
    @property
    def exclude(self) -> bool:
        """Check if the shape is excluded"""
        return self._rust_shape.get_exclude()
    
    def __repr__(self) -> str:
        """String representation of the shape"""
        excluded = '-' if self.exclude else ''
        props_str = f", properties={self.properties}" if self.properties else ""
        tags_str = f", tags={self.tags}" if self.tags else ""
        return f"Shape({excluded}{self.shape_type}({', '.join(map(str, self.coordinates))}){props_str}{tags_str})"


class Region:
    """A collection of shapes parsed from a region file"""
    
    def __init__(self):
        """Initialize an empty region"""
        self.shapes: List[Shape] = []
        self.global_properties: Dict[str, Any] = {}
        self.comments: List[str] = []
        
    def add_shape(self, shape: Shape) -> None:
        """Add a shape to the region"""
        self.shapes.append(shape)
        
    def add_comment(self, comment: str) -> None:
        """Add a comment to the region"""
        self.comments.append(comment)
        
    def update_global_properties(self, properties: Dict[str, Any]) -> None:
        """Update global properties"""
        self.global_properties.update(properties)
        
    def __len__(self) -> int:
        """Number of shapes in the region"""
        return len(self.shapes)
    
    def __getitem__(self, idx) -> Shape:
        """Get a shape by index"""
        return self.shapes[idx]
    
    def __iter__(self):
        """Iterate over shapes"""
        return iter(self.shapes)
    
    def __repr__(self) -> str:
        """String representation of the region"""
        shapes_str = "\n  ".join(repr(shape) for shape in self.shapes)
        global_str = f"\nGlobal properties: {self.global_properties}" if self.global_properties else ""
        comments_str = f"\nComments: {self.comments}" if self.comments else ""
        return f"Region with {len(self.shapes)} shapes:{global_str}{comments_str}\n  {shapes_str}"
