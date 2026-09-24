"""Explicit correspondence between canonical modules and the older checked edition."""
import json
from pathlib import Path

LAYOUT = json.loads((Path(__file__).resolve().parents[1] / 'agda/module-layout.json').read_text(encoding='utf-8'))


def canonical_module(previous):
    return LAYOUT['modules'].get(previous, previous)


def previous_module(canonical, qualified):
    for entry in LAYOUT['declarations']:
        if entry['canonical_module'] == canonical and entry['qualified'] == qualified:
            return entry['previous_module']
    matches = [old for old, new in LAYOUT['modules'].items() if new == canonical]
    if len(matches) > 1:
        raise ValueError('Ambiguous older module: ' + canonical)
    return matches[0] if matches else canonical
