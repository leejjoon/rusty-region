import rusty_region_parser # Use the name specified in pyproject.toml or Cargo.toml [lib]

line1 = "circle(100, 200, 30)"
line2 = "ellipse( 500, 500, 20, 10, 45 ) # color=red tag={cluster 1}"
line3 = "invalid line("

shape1 = rusty_region_parser.parse_region_line(line1)
print(f"Parsed shape: {shape1.shape_type_str}")
print(f"Coordinates: {shape1.coordinates}")
print(f"Properties: {[(p.key, p.value) for p in shape1.properties]}") # Access properties

shape2 = rusty_region_parser.parse_region_line(line2)
print(f"\nParsed shape: {shape2.shape_type_str}")
print(f"Coordinates: {shape2.coordinates}")
# Access properties via the automatically generated getters
for prop in shape2.properties:
     print(f" - Property: key='{prop.key}', value='{prop.value}'")


try:

    shape3 = rusty_region_parser.parse_region_line(line3) # This will raise ValueError

except ValueError as e:
    print(f"\nFailed to parse line 3: {e}")
