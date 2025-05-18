import pytest
import numpy as np
from rusty_region import parse_region_string
from rusty_region.region import FormatType


def test_format_enum_values():
    """Test that the FormatType enum has the expected integer values"""
    assert FormatType.SIMPLE == 0
    assert FormatType.SEXAGESIMAL_COLON == 1
    assert FormatType.SEXAGESIMAL_HMS == 2
    assert FormatType.SEXAGESIMAL_DMS == 3
    assert FormatType.WITH_UNIT == 4


def test_format_type_conversion():
    """Test converting between integer values and FormatType enum"""
    # Convert from integer to enum
    assert FormatType(0) == FormatType.SIMPLE
    assert FormatType(1) == FormatType.SEXAGESIMAL_COLON
    assert FormatType(2) == FormatType.SEXAGESIMAL_HMS
    assert FormatType(3) == FormatType.SEXAGESIMAL_DMS
    assert FormatType(4) == FormatType.WITH_UNIT
    
    # Convert from enum to integer
    assert int(FormatType.SIMPLE) == 0
    assert int(FormatType.SEXAGESIMAL_COLON) == 1
    assert int(FormatType.SEXAGESIMAL_HMS) == 2
    assert int(FormatType.SEXAGESIMAL_DMS) == 3
    assert int(FormatType.WITH_UNIT) == 4
