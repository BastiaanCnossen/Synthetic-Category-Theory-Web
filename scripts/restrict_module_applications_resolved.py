"""Add `using (...)` lists to module applications, following downstream aliases.

Usage:
  python scripts/restrict_module_applications_resolved.py agda/src [--dry-run] [--report FILE]
      [--large-only] [path-prefix ...]

--large-only restricts only applications whose arguments contain a projection
`A.x` or parentheses (instantiations at plain variables are cheap; GUIDELINES A2).

Successor of restrict_module_applications.py. That script skips an
application `module X = M args` as soon as the name `X` occurs anywhere in a
transitive importer, because a later module might reach names through it.
This script instead resolves *how* later modules reach `X`, and adds those
names to the `using` list as well:

  * qualified uses `X.a`, `Outer.X.a`, `N.X.a` (with `import m … as N`);
  * imports `open import m … using (module X)` and `… public` re-exports,
    followed transitively;
  * module aliases `module H = <handle>` (then `H.a`), and
    `module H = <handle>.Sub` (then `module Sub` is needed);
  * `open <handle> using (a; module B)` and `open <handle>.Sub`;
  * wholesale `open <handle>`: the used names are approximated by the exports
    of `M` that occur as tokens in the opening file (and, for `open … public`,
    in its transitive importers). An operator `_∙_` counts as used if all its
    name parts occur as tokens.

The analysis is static and approximate, in both directions:
  * a name it misses gives an Agda error "… is not in scope" or
    "… is not exported";
  * a name it adds that the module does not export gives
    "The module … doesn't export the following: …".
Both are loud, never silent, so the result is safe to try. Use
--dry-run --report FILE to see what would change.
Applications that are `private` cannot be reached downstream and are resolved
locally only. Applications whose handles escape in a way the script cannot
follow (e.g. passed to a further module application with arguments, or
re-opened wholesale where `M`'s exports cannot be determined) are skipped and
reported.

Path prefixes accept either slash convention. Line endings are preserved.
"""
import json
import os
import re
import sys
from collections import defaultdict

NAME = r"[^\s(){}.;\"@]+"
ID = re.compile(r"[^\s(){}.;\"@]+")


def parse_args(argv):
    src, dry, report, only, large = None, False, None, [], False
    it = iter(argv)
    for a in it:
        if a == "--dry-run":
            dry = True
        elif a == "--large-only":
            large = True
        elif a == "--report":
            report = next(it)
        elif src is None:
            src = a
        else:
            only.append(a.replace("\\", "/"))
    if src is None:
        sys.exit(__doc__)
    return src, dry, report, only, large


SRC, DRY, REPORT, ONLY, LARGE_ONLY = parse_args(sys.argv[1:])


def rel(p):
    return os.path.relpath(p, SRC).replace("\\", "/")


def modname(p):
    return rel(p).removesuffix(".lagda.md").removesuffix(".agda").replace("/", ".")


def code_spans(text, path):
    if path.endswith(".lagda.md"):
        return [(m.start(1), m.end(1)) for m in re.finditer(r"```agda\r?\n(.*?)```", text, re.S)]
    return [(0, len(text))]


def strip_comments(s):
    s = re.sub(r"\{-.*?-\}", lambda m: re.sub(r"[^\n]", " ", m.group(0)), s, flags=re.S)
    return re.sub(r"--[^\n]*", "", s)


files, code, path_of = {}, {}, {}
for dp, _, fs in os.walk(SRC):
    for f in fs:
        if f.endswith(".lagda.md") or f.endswith(".agda"):
            p = os.path.join(dp, f)
            t = open(p, encoding="utf8", newline="").read()
            files[p] = t
            m = modname(p)
            path_of[m] = p
            code[m] = strip_comments("\n".join(t[a:b] for a, b in code_spans(t, p))).replace("\r", "")

# ---------------------------------------------------------------- imports

IMPORT = re.compile(
    r"^[ \t]*(open[ \t]+)?import[ \t]+(SCT\.[\w.]+)((?:[^\n]|\n[ \t]+(?!open\b|import\b|module\b))*)",
    re.M)


def import_items(clause):
    """Parse `using (...)`, `hiding`, `renaming`, `as N`, `public` of an import line."""
    d = {"using": None, "hiding": [], "renaming": {}, "as": None,
         "public": bool(re.search(r"\bpublic\b", clause))}
    u = re.search(r"\busing\s*\(([^)]*)\)", clause)
    if u:
        d["using"] = [x.strip() for x in u.group(1).split(";") if x.strip()]
    h = re.search(r"\bhiding\s*\(([^)]*)\)", clause)
    if h:
        d["hiding"] = [x.strip() for x in h.group(1).split(";") if x.strip()]
    r = re.search(r"\brenaming\s*\(([^)]*)\)", clause)
    if r:
        for x in r.group(1).split(";"):
            if " to " in x:
                a, b = x.split(" to ", 1)
                d["renaming"][a.strip()] = b.strip()
    a = re.search(r"\bas\s+(" + NAME + ")", clause)
    if a:
        d["as"] = a.group(1)
    return d


imports = defaultdict(list)          # importer -> [(imported, opened, items)]
importers = defaultdict(set)         # imported -> {importer}
for m, c in code.items():
    for x in IMPORT.finditer(c):
        tgt = x.group(2)
        if tgt not in code:
            continue
        imports[m].append((tgt, bool(x.group(1)), import_items(x.group(3))))
        importers[tgt].add(m)
    # `import M` followed by `module N = M args` / `open M args`
    for x in re.finditer(r"^[ \t]*module[ \t]+(" + NAME + r")[ \t]*=[ \t]*(SCT\.[\w.]+)\b", c, re.M):
        pass  # handled as an alias in handle resolution below


def visible_name(items, first):
    """How does a top-level name `first` of the imported module appear in the importer?"""
    if items["using"] is not None:
        if first not in items["using"] and ("module " + first) not in items["using"]:
            return None
    if first in items["hiding"] or ("module " + first) in items["hiding"]:
        return None
    ren = items["renaming"].get("module " + first) or items["renaming"].get(first)
    if ren:
        return ren.removeprefix("module ").strip()
    return first


# ---------------------------------------------------------------- exports

export_cache = {}
SIG = re.compile(r"^([ \t]*)(?:(?:data|record)[ \t]+)?(" + NAME + r")[ \t]*:", re.M)


def block_body(c, header_regex):
    """Lines of the module block introduced by a header matching header_regex."""
    lines = c.split("\n")
    for i, l in enumerate(lines):
        if re.match(header_regex, l):
            ind = len(l) - len(l.lstrip())
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > ind):
                j += 1
            body = lines[i + 1:j]
            return body
    return None


def exports(target):
    """Approximate set of names exported by module `target` (maybe `Mod.Sub.Sub2`).

    Returns None when it cannot be determined."""
    if target in export_cache:
        return export_cache[target]
    export_cache[target] = None
    parts = target.split(".")
    for k in range(len(parts), 0, -1):
        top = ".".join(parts[:k])
        if top in code:
            break
    else:
        return None
    c, subs = code[top], parts[k:]
    lines = c.split("\n")
    if subs:
        body = c
        for s in subs:
            b = block_body(body, r"^\s*module\s+" + re.escape(s) + r"\b(?!\s*=)")
            if b is None:
                return None
            body = "\n".join(b)
        lines = body.split("\n")
    nonempty = [l for l in lines if l.strip() and not l.lstrip().startswith(("open", "import", "{-#", "module " + "_"))]
    if not nonempty:
        return None
    base = min(len(l) - len(l.lstrip()) for l in nonempty)
    names = set()
    stack = []   # (indent, header) of enclosing blocks below the base level
    for l in lines:
        if not l.strip():
            continue
        ind = len(l) - len(l.lstrip())
        while stack and ind <= stack[-1][0]:
            stack.pop()
        s = l.strip()
        hidden = any(h == "private" or not EXPORTING.match(h) for _, h in stack)
        if ind > base and not stack:
            continue   # continuation of a declaration at the base level
        if hidden:
            if re.match(r"(private|abstract|opaque|instance|mutual|module\s+_\b.*where|where)\s*$", s) or s.endswith(" where"):
                stack.append((ind, s))
            continue
        if re.match(r"(private|abstract|opaque|instance|mutual)\s*$", s) or re.match(r"module\s+_\b.*where\s*$", s):
            stack.append((ind, s))
            continue
        m = re.match(r"(?:(?:data|record)\s+)?(" + NAME + r")\s*:", s)
        if m:
            names.add(m.group(1))
        m = re.match(r"(?:data|record)\s+(" + NAME + r")\b", s)
        if m:
            names.add(m.group(1))
            names.add("module " + m.group(1))
        m = re.match(r"module\s+(" + NAME + r")\b", s)
        if m and m.group(1) != "_":
            names.add("module " + m.group(1))
            if s.endswith("where"):
                stack.append((ind, "named"))
        m = re.match(r"(" + NAME + r")\b[^=:]*?\s=(\s|$)", s)
        if m and m.group(1) not in KEYWORDS:
            names.add(m.group(1))   # definitions without a type signature
        m = re.match(r"constructor\s+(" + NAME + r")", s)
        if m:
            names.add(m.group(1))
        m = re.match(r"open\s+import\s+(SCT\.[\w.]+)(.*)$", s)
        if m and "public" in m.group(2):
            sub = exports(m.group(1))
            if sub is None:
                return None
            it = import_items(m.group(2))
            for n in sub:
                v = visible_name(it, n.removeprefix("module "))
                if v:
                    names.add(("module " + v) if n.startswith("module ") else v)
        elif re.match(r"open\s+\S+.*\bpublic\b", s):
            return None   # re-export of a local module: not followed
        elif s.endswith(" where") or s == "where":
            stack.append((ind, "named"))
    export_cache[target] = names
    return names


def used_by_tokens(names, text):
    toks = set(ID.findall(text))
    out = set()
    for n in names:
        if n.startswith("module "):
            if re.search(r"\b" + re.escape(n[7:]) + r"\.", text):
                out.add(n)
            continue
        parts = [x for x in n.split("_") if x]
        if n in toks or (parts and all(x in toks for x in parts)):
            out.add(n)
    return out


# ---------------------------------------------------------------- handles

KEYWORDS = {"module", "open", "import", "data", "record", "field", "constructor", "where", "with",
            "rewrite", "let", "in", "pattern", "syntax", "infix", "infixl", "infixr", "postulate"}
EXPORTING = re.compile(r"(abstract|opaque|instance|mutual|module\s+_\b.*)$")


class Unresolvable(Exception):
    pass


def uses_through(handle, mod, seen, text=None):
    """Names reached through `handle` (a dotted name denoting the application) in module `mod`.

    Returns a set of items `a` / `module B`; raises Unresolvable."""
    key = (handle, mod)
    if key in seen:
        return set()
    seen.add(key)
    c = code[mod] if text is None else text
    h = re.escape(handle)
    out = set()
    pre = r"(?<![^\s(){};@])"
    # module aliases first, to classify their targets as modules
    for x in re.finditer(r"^[ \t]*module[ \t]+(" + NAME + r")[ \t]*=[ \t]*" + h + r"(\.(" + NAME + r"))?(?=[\s;)]|$)([^\n]*)", c, re.M):
        alias, sub, rest = x.group(1), x.group(3), x.group(4)
        if sub:
            out.add("module " + sub.split(".")[0])
            continue
        if rest.strip() and not re.match(r"\s*(using|hiding|renaming)\b", rest):
            raise Unresolvable(f"{mod}: alias {alias} applies {handle} to further arguments")
        it = import_items(rest)
        if it["using"] is not None:
            out |= set(it["using"])
        else:
            out |= uses_through(alias, mod, seen)
            out |= downstream(mod, alias, seen, private=False)
    for x in re.finditer(r"^[ \t]*open[ \t]+" + h + r"(\.(" + NAME + r"))?(?=[\s;)]|$)([^\n]*)", c, re.M):
        sub, rest = x.group(2), x.group(3)
        if sub:
            out.add("module " + sub)
            continue
        it = import_items(rest)
        if it["using"] is not None:
            out |= set(it["using"])
            if it["public"]:
                pass  # names re-exported: their downstream use needs no module X
            continue
        raise Unresolvable(f"{mod}: wholesale `open {handle}`")
    # instantiations of an enclosing module: `module L = Prefix args` makes `L.Rest` a handle
    parts = handle.split(".")
    for i in range(1, len(parts)):
        prefix, rest = ".".join(parts[:i]), ".".join(parts[i:])
        for x in re.finditer(r"^[ \t]*module[ \t]+(" + NAME + r")[ \t]*=[ \t]*" + re.escape(prefix) + r"(?=[\s;)]|$)([^\n]*)", c, re.M):
            it = import_items(x.group(2))
            first = rest.split(".")[0]
            if it["using"] is not None and first not in it["using"] and ("module " + first) not in it["using"]:
                continue
            out |= uses_through(x.group(1) + "." + rest, mod, seen, text)
            out |= downstream(mod, x.group(1) + "." + rest, seen, private=False)
    for x in re.finditer(pre + h + r"\.(" + NAME + r")(\.)?", c):
        line = c[c.rfind("\n", 0, x.start()) + 1:x.start()]
        if re.match(r"\s*(open|module\s+" + NAME + r"\s*=)\s*$", line):
            continue  # handled above
        n = x.group(1)
        out.add(("module " + n) if x.group(2) else n)
    return out


def downstream(mod, name, seen, private):
    """Names reached through the top-level name `name` of `mod` by importers."""
    if private:
        return set()
    out = set()
    first = name.split(".")[0]
    for q in importers.get(mod, ()):
        for tgt, opened, it in imports[q]:
            if tgt != mod:
                continue
            handles = []
            if it["as"]:
                handles.append(it["as"] + "." + name)
            handles.append(mod + "." + name)
            if opened:
                v = visible_name(it, first)
                if v:
                    handles.append(".".join([v] + name.split(".")[1:]))
                    if it["public"]:
                        out |= downstream(q, ".".join([v] + name.split(".")[1:]), seen, False)
            for hd in handles:
                out |= uses_through(hd, q, seen)
        # `import mod` then `module N = mod args`
        for x in re.finditer(r"^[ \t]*module[ \t]+(" + NAME + r")[ \t]*=[ \t]*" + re.escape(mod) + r"\b", code[q], re.M):
            out |= uses_through(x.group(1) + "." + name, q, seen)
    return out


# ---------------------------------------------------------------- applications

def enclosing(lines, i):
    """Enclosing named modules of line i, and whether it is private."""
    ind = len(lines[i]) - len(lines[i].lstrip())
    path, private = [], False
    for j in range(i - 1, -1, -1):
        l = lines[j]
        if not l.strip():
            continue
        k = len(l) - len(l.lstrip())
        if k < ind:
            s = l.strip()
            if s == "private":
                private = True
            m = re.match(r"module\s+(" + NAME + r")\b(?!\s*=)", s)
            if m and not s.startswith("module SCT."):
                if m.group(1) != "_":
                    path.insert(0, m.group(1))
            ind = k
            if k == 0:
                break
    return path, private


TRANSPARENT = re.compile(r"(private|abstract|opaque|instance|mutual|where|module\s+_\b.*)$")


def scope_indent(lines, i):
    """(indentation, line) of the header whose scope contains line i: an enclosing named
    module, or the definition owning a `where` block. (-1, 0) at the top level."""
    ind = len(lines[i]) - len(lines[i].lstrip())
    for j in range(i - 1, -1, -1):
        l = lines[j]
        if not l.strip():
            continue
        k = len(l) - len(l.lstrip())
        if k < ind:
            st = l.strip()
            if not TRANSPARENT.match(st) and not st.startswith("unfolding"):
                if st.startswith("module SCT."):
                    return -1, 0
                # a `where` block belongs to the clause it ends: the region starts there
                start = j
                return k, start
            ind = k
    return -1, 0


stats = defaultdict(int)
report = []
changed = []
for p, text in sorted(files.items()):
    r = rel(p)
    if ONLY and not any(r.startswith(o) for o in ONLY):
        continue
    mod = modname(p)
    edits = []
    spans = code_spans(text, p)
    for bi_, (a, b) in enumerate(spans):
        blk = text[a:b]
        lines = blk.split("\n")
        offs = [0]
        for ln in lines:
            offs.append(offs[-1] + len(ln) + 1)
        i = 0
        while i < len(lines):
            m = re.match(r"^(\s*)module\s+(" + NAME + r")\s*=\s*(\S.*)$", lines[i].rstrip("\r"))
            if not m:
                i += 1
                continue
            ind, X = len(m.group(1)), m.group(2)
            j = i + 1
            while j < len(lines) and lines[j].strip() and len(lines[j]) - len(lines[j].lstrip()) > ind:
                j += 1
            rhs = " ".join(l.strip() for l in lines[i:j])
            stats["apps"] += 1
            target = rhs.split("=", 1)[1].split()[0]
            args = rhs.split("=", 1)[1].split()[1:]
            if X == "_" or re.search(r"\b(using|hiding|renaming|public)\b", rhs):
                stats["already_restricted"] += 1
                i = j
                continue
            if not args:
                stats["plain_alias"] += 1   # `module H = Input.H`: copies nothing new
                i = j
                continue
            argtext = rhs.split("=", 1)[1].split(None, 1)[1] if len(rhs.split("=", 1)[1].split(None, 1)) > 1 else ""
            if LARGE_ONLY and not re.search(r"[().]", argtext):
                stats["skipped_variable_args"] += 1   # cheap: instantiated at variables (A2)
                i = j
                continue
            path, private = enclosing(lines, i)
            seen = set()
            # local uses: only the rest of the block that contains the application,
            # since sibling submodules often reuse the same local name
            h, start = scope_indent(lines, i)
            if h < 0:
                start = i
            k = j
            while k < len(lines) and (not lines[k].strip() or len(lines[k]) - len(lines[k].lstrip()) > h):
                k += 1
            extra = []
            if k == len(lines):
                # the scope continues into the following code blocks of a literate file
                for a2, b2 in spans[bi_ + 1:]:
                    stop = False
                    for l2 in text[a2:b2].split("\n"):
                        if l2.strip() and len(l2) - len(l2.lstrip()) <= h:
                            stop = True
                            break
                        extra.append(l2)
                    if stop:
                        break
            region = strip_comments("\n".join(lines[start:k] + extra)).replace("\r", "")
            try:
                used = uses_through(X, mod, seen, region)
                full = ".".join(path + [X])
                if path:
                    used |= uses_through(full, mod, seen)
                used |= downstream(mod, full, seen, private)
            except Unresolvable as e:
                stats["skipped_unresolvable"] += 1
                report.append({"module": mod, "app": X, "action": "skipped", "reason": str(e)})
                i = j
                continue
            if not used:
                stats["skipped_unused"] += 1
                report.append({"module": mod, "app": X, "action": "skipped", "reason": "no uses found"})
                i = j
                continue
            plain = sorted(n for n in used if not n.startswith("module "))
            mods = sorted(n[7:] for n in used if n.startswith("module "))
            items = plain + ["module " + n for n in mods if n not in plain]
            eol = "\r\n" if "\r\n" in text else "\n"
            clause = eol + " " * (ind + 2) + "using (" + "; ".join(items) + ")"
            end = j - 1
            pos = a + offs[end] + len(lines[end].rstrip("\r"))
            edits.append((pos, clause))
            stats["restricted"] += 1
            report.append({"module": mod, "app": X, "target": target, "action": "restricted",
                           "names": items, "private": private})
            i = j
    if edits and not DRY:
        for pos, clause in sorted(edits, reverse=True):
            text = text[:pos] + clause + text[pos:]
        open(p, "w", encoding="utf8", newline="").write(text)
    if edits:
        changed.append(r)
if REPORT:
    json.dump(report, open(REPORT, "w"), indent=1, ensure_ascii=False)
print(json.dumps(dict(stats)), len(changed), "files", "would change" if DRY else "changed")
