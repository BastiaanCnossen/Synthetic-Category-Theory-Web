"""Add `using (...)` to parameterized module applications `module X = M args`.

Usage:  python scripts/restrict_module_applications.py agda/src [path-prefix ...]
e.g.    python scripts/restrict_module_applications.py agda/src SCT/VolumeI/Chapter02/Section02

Path prefixes accept either slash convention.

Rewrites files in place (preserving line endings); run it on a clean git
state so the diff can be reviewed, then check the affected modules.
Applications that may be reached from downstream modules (their name occurs
qualified or in a using-list in any transitive importer) are left alone.

For each application without using/hiding/renaming/public, collect every name
reached through `X.` (in this file and, conservatively, in every file that
imports this module), and restrict the application to exactly those names.
`X.a.b...` means `a` is a submodule, so it becomes `module a`. Applications
that are opened wholesale (`open X` without using) are left alone.
"""
import re, os, sys, json

SRC = sys.argv[1]
only = [prefix.replace("\\", "/") for prefix in sys.argv[2:]]  # relative to SRC

def relative_path(p):
    """Use one slash convention for module names and prefix selection."""
    return os.path.relpath(p, SRC).replace("\\", "/")

def code_blocks(text, path):
    if path.endswith('.lagda.md'):
        return [(m.start(1), m.end(1)) for m in re.finditer(r'```agda\r?\n(.*?)```', text, re.S)]
    return [(0, len(text))]

files = {}
for dp, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith('.lagda.md') or f.endswith('.agda'):
            p = os.path.join(dp, f)
            files[p] = open(p, encoding='utf8', newline='').read()

def modname(p):
    r = relative_path(p)
    return r.removesuffix('.lagda.md').removesuffix('.agda').replace('/', '.')

importers = {}
for p, t in files.items():
    for m in set(re.findall(r'\bimport\s+(SCT\.[\w.]+)', t)):
        importers.setdefault(m, set()).add(p)

NAME = r"[^\s(){}.;\"@]+"
rev_cache = {}
def rev_closure(m):
    if m in rev_cache: return rev_cache[m]
    seen, stack = set(), [m]
    while stack:
        x = stack.pop()
        for q in importers.get(x, ()):
            if q not in seen:
                seen.add(q); stack.append(modname(q))
    rev_cache[m] = seen
    return seen
def used_downstream(X, m):
    pats = [r'module\s+' + re.escape(X) + r'\s*[;)]', r'\.' + re.escape(X) + r'(?=[.\s)]|$)']
    return any(re.search(pt, files[q], re.M) for q in rev_closure(m) for pt in pats)

stats = {'apps': 0, 'restricted': 0, 'skipped_open': 0, 'skipped_other': 0}
changed = []
for p, text in files.items():
    rel = relative_path(p)
    if only and not any(rel.startswith(o) for o in only):
        continue
    blocks = code_blocks(text, p)
    edits = []
    for (a, b) in blocks:
        blk = text[a:b]
        lines = blk.split('\n')
        offs = [0]
        for ln in lines: offs.append(offs[-1] + len(ln) + 1)
        i = 0
        while i < len(lines):
            m = re.match(r'^(\s*)module\s+(' + NAME + r')\s*=\s*(\S.*)$', lines[i])
            if not m:
                i += 1; continue
            ind = len(m.group(1)); X = m.group(2)
            j = i + 1
            while j < len(lines) and lines[j].strip() and (len(lines[j]) - len(lines[j].lstrip())) > ind:
                j += 1
            rhs = ' '.join(l.strip() for l in lines[i:j])
            stats['apps'] += 1
            if re.search(r'\b(using|hiding|renaming|public)\b', rhs) or X == '_':
                i = j; continue
            # uses in this file and in importers of this module
            scope = [text] + [files[q] for q in importers.get(modname(p), ())]
            if any(re.search(r'\bopen\s+' + re.escape(X) + r'(\s*$|\s+(?!using)[^\n]*$)', s, re.M) for s in scope) or \
               any(re.search(r'\bopen\s+' + re.escape(X) + r'\s*\n', s) for s in scope):
                stats['skipped_open'] += 1; i = j; continue
            if used_downstream(X, modname(p)):
                stats['skipped_downstream'] = stats.get('skipped_downstream', 0) + 1; i = j; continue
            scope = [text]
            names, mods = set(), set()
            ok = True
            for k, s in enumerate(scope):
                pre = r'(?<![\w.])' if k == 0 else r'(?<=\.)'
                for u in re.finditer(pre + re.escape(X) + r'\.(' + NAME + r')(\.' + NAME + r')?', s):
                    if u.group(2): mods.add(u.group(1))
                    else: names.add(u.group(1))
                # `open X using (a; b)` / `open X.Sub`
                for u in re.finditer(r'\bopen\s+' + re.escape(X) + r'\s+using\s*\(([^)]*)\)', s):
                    for n in u.group(1).split(';'):
                        n = n.strip()
                        if n.startswith('module '): mods.add(n[7:].strip())
                        elif n: names.add(n)
            # names used as `module Y = X.name` / `open X.name` are modules
            for s in scope:
                for u in re.finditer(r'(?:\bmodule\s+' + NAME + r'\s*=|\bopen)\s+' + re.escape(X) + r'\.(' + NAME + r')(?=\s)', s):
                    if u.group(1) in names:
                        names.discard(u.group(1)); mods.add(u.group(1))
            if not names and not mods:
                stats['skipped_other'] += 1; i = j; continue
            items = sorted(names) + ['module ' + n for n in sorted(mods)]
            eol = '\r\n' if '\r\n' in text else '\n'
            clause = eol + ' ' * (ind + 2) + 'using (' + '; '.join(items) + ')'
            end_line = j - 1
            pos = a + offs[end_line] + len(lines[end_line].rstrip('\r'))
            edits.append((pos, clause))
            stats['restricted'] += 1
            i = j
    if edits:
        for pos, clause in sorted(edits, reverse=True):
            text = text[:pos] + clause + text[pos:]
        open(p, 'w', encoding='utf8', newline='').write(text)
        changed.append(rel)
print(json.dumps(stats), len(changed), 'files changed')
