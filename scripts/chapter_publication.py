"""Audit a proposed chapter selection before importing compiler output.

This is a structural/source audit, never an Agda verification receipt. Sources
must be extracted from the intended commit, separately from the working tree.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re


def source_inventory(root):
    result = {}
    for path in sorted(Path(root).rglob('*')):
        if not (path.name.endswith('.agda') or path.name.endswith('.lagda.md')):
            continue
        relative = path.relative_to(root).as_posix()
        name = relative.removesuffix('.lagda.md').removesuffix('.agda').replace('/', '.')
        if name in result:
            raise ValueError('Duplicate module: ' + name)
        raw = path.read_bytes()
        source = raw.decode('utf-8').replace('\r\n', '\n')
        code = '\n'.join(re.findall(r'```agda\s*\n(.*?)```', source, re.S)) if '```agda' in source else source
        result[name] = {'source': relative, 'sha256': hashlib.sha256(raw).hexdigest(),
                        'text_sha256': hashlib.sha256(source.encode()).hexdigest(),
                        'imports': set(re.findall(r'\bimport (SCT\.[\w.]+)', code))}
    return result


def select_chapter(modules, chapter, excluded):
    """Exclude roots and their dependents, never publish an incomplete closure."""
    prefix = f'SCT.VolumeI.Chapter{chapter:02d}.'
    chapter_names = {name for name in modules if name.startswith(prefix)}
    unknown = set(excluded) - modules.keys()
    if unknown:
        raise ValueError('Unknown exclusion roots: ' + ', '.join(sorted(unknown)))
    reasons = {name: {name} for name in excluded}
    while True:
        changed = False
        for name, data in modules.items():
            inherited = set().union(*(reasons.get(dep, set()) for dep in data['imports']))
            expanded = reasons.get(name, set()) | inherited
            if expanded and expanded != reasons.get(name, set()):
                reasons[name] = expanded
                changed = True
        if not changed:
            break
    roots = sorted(n for n in chapter_names - reasons.keys() if not n.endswith('.Everything'))
    selected = set()
    def visit(name):
        if name in selected:
            return
        if name not in modules:
            raise ValueError('Missing prerequisite: ' + name)
        if name in reasons:
            raise ValueError('Excluded prerequisite selected: ' + name)
        selected.add(name)
        for dependency in modules[name]['imports']:
            visit(dependency)
    for root in roots:
        visit(root)
    return {'chapter': chapter, 'selected_modules': sorted(selected),
            'excluded_modules': {name: sorted(reasons[name]) for name in sorted(chapter_names & reasons.keys())},
            'skipped_aggregates': sorted(n for n in chapter_names - selected - reasons.keys()),
            'source_hashes': {n: modules[n]['sha256'] for n in sorted(selected)}}


def passage_impact(registries, modules, selected, chapter):
    """Keep missing/moved targets distinct from deliberate verification omissions."""
    result = []
    prefix = f'SCT.VolumeI.Chapter{chapter:02d}.'
    for label, registry in registries:
        for passage in registry.get('passages', []) + registry.get('reverse_only', []):
            targets = []
            for d in passage['declarations']:
                name = d['module'] if d['module'].startswith('SCT.') else registry.get('module_prefix', 'SCT.VolumeI.') + d['module']
                if not name.startswith(prefix) or name in selected:
                    continue
                targets.append({'module': name, 'declaration': d['qualified'],
                                'reason': 'omitted' if name in modules else 'missing-or-moved'})
            if targets:
                result.append({'registry': label, 'passage': passage['id'], 'page': passage['page'], 'targets': targets})
    return result


def compare_checked_sources(modules, selected, expected, checked=None):
    mismatches, normalized = [], []
    for name in sorted(selected):
        if name not in expected:
            continue
        if expected[name] == modules[name]['sha256']:
            continue
        current = (checked or {}).get(name)
        if (current and current['sha256'] == expected[name]
                and current['text_sha256'] == modules[name]['text_sha256']):
            normalized.append(name)
        else:
            mismatches.append(name)
    return mismatches, normalized


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', required=True, type=Path)
    parser.add_argument('--plan', required=True, type=Path)
    parser.add_argument('--checked-source-root', type=Path,
                        help='Optional exact checked working tree, to audit CRLF-only differences.')
    parser.add_argument('--chapter', type=int, default=1)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    plan = json.loads(args.plan.read_text(encoding='utf-8'))
    modules = source_inventory(args.source_root)
    # Working-tree-only modules in a checker plan are explicitly excluded from
    # this committed source selection, without pretending they were committed.
    excluded = set(plan['excluded_modules']) & modules.keys()
    result = select_chapter(modules, args.chapter, excluded)
    registries = [('book', json.loads((root/'correspondence.json').read_text(encoding='utf-8')))]
    registries += [(n['slug'], n) for n in json.loads((root/'Supplementary notes/notes.json').read_text(encoding='utf-8'))]
    result['passage_impact'] = passage_impact(registries, modules, set(result['selected_modules']), args.chapter)
    result['uncommitted_plan_modules'] = sorted(set(plan.get('safe_modules', [])) - modules.keys())
    checked = source_inventory(args.checked_source_root) if args.checked_source_root else None
    result['plan_source_mismatches'], result['line_ending_only_matches'] = compare_checked_sources(
        modules, result['selected_modules'], plan.get('source_hashes', {}), checked)
    result['status'] = 'structural audit only; compiler evidence required'
    result['plan_status'] = plan.get('status', 'unspecified')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({key: len(result[key]) for key in ('selected_modules', 'excluded_modules',
        'passage_impact', 'uncommitted_plan_modules', 'plan_source_mismatches')}))


if __name__ == '__main__':
    main()
