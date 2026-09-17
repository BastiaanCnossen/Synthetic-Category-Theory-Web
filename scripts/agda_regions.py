"""Stable, non-nested Agda display regions delimited by comment lines.

Offsets use Python string indices into the unmodified input. The opening and
closing marker lines are excluded; whitespace inside the region is retained.
Region names identify code, independently of book passages or publication paths.
"""
import re


_MARKER = re.compile(r"^[ \t]*--! (begin|end) ([a-z][a-z0-9-]*)[ \t]*(?:\r?\n|$)")


def region_ranges(source):
    """Return ``{name: {'start': int, 'end': int}}`` or reject invalid markers.

Regions may be adjacent, but cannot nest, cross, repeat, or be empty. A line
beginning with ``--!`` is reserved for this syntax and must be a valid marker.
"""
    regions = {}
    active = None
    offset = 0
    for line in source.splitlines(keepends=True):
        if line.lstrip(' \t').startswith('--!'):
            match = _MARKER.fullmatch(line)
            if not match:
                raise ValueError(f'Malformed Agda region marker at offset {offset}')
            kind, name = match.groups()
            if kind == 'begin':
                if active is not None:
                    raise ValueError(f'Nested Agda region {name} inside {active[0]}')
                if name in regions:
                    raise ValueError(f'Duplicate Agda region {name}')
                active = (name, offset + len(line))
            else:
                if active is None:
                    raise ValueError(f'Unmatched Agda region end {name}')
                if name != active[0]:
                    raise ValueError(f'Crossed Agda region end {name}; expected {active[0]}')
                if not source[active[1]:offset].strip():
                    raise ValueError(f'Empty Agda region {name}')
                regions[name] = {'start': active[1], 'end': offset}
                active = None
        offset += len(line)
    if active is not None:
        raise ValueError(f'Unclosed Agda region {active[0]}')
    return regions
