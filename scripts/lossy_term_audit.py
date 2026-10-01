"""Generate a module that checks that --lossy-unification did not change any term.

Usage:
  python scripts/lossy_term_audit.py agda/src SCT.Some.Module [SCT.Other.Module ...]

For each flagged module `SCT.A.B`, this writes
`agda/src/SCT/Scratch/LossyAudit/A/B.agda`, module `SCT.Scratch.LossyAudit.A.B`:

  * a copy of the module's code *without* `--lossy-unification` (literate
    Markdown is flattened to plain Agda, which is equivalent);
  * an import of the original (lossy) module at the same parameters,
    `import SCT.A.B <params> as Lossy′`;
  * for every exported definition `d : T` (top level, inside named or
    anonymous submodules, inside `instance`), a check, placed at the end of
    the block that contains `d`:

        _ : Eqᴸ._≡_ {A = T} d (Lossy′.Path.d <submodule arguments>)
        _ = Eqᴸ.refl

    where `Eqᴸ` is Agda.Builtin.Equality.

Checking the generated module (an ordinary `agda` run) then establishes that
each definition elaborated without the flag is *definitionally* equal to the
one elaborated with it. Agda compares the two terms after unfolding, so this
is weaker than syntactic identity but it is exactly the equality the rest of
the development can observe. Compare LESSONS.md L4.

Not compared, and listed at the end of the generated file:
  * definitions in `private` blocks (invisible from outside);
  * for definitions in `abstract` and `opaque` blocks only the *types* are
    compared (`_ : T` / `_ = Lossy′.d …`): their terms cannot be observed
    downstream, but their types can, and types are elaborated with the flag too;
  * definitions without a type signature, and signatures mentioning `Level`
    or `Set ω` (the builtin identity type needs a small type);
  * module applications `module X = M args` (their arguments are elaborated
    in the module, but are only observable through the definitions that use
    them, which are compared);
  * records, data types and fields.

If the copy without the flag does not check at all, that is the finding
(and `scripts/audit_lossy.py` would already report it).
"""
import os
import re
import sys

NAME = r"[^\s(){}.;\"@]+"


def code_of(path):
    s = open(path, encoding="utf8", newline="").read().replace("\r\n", "\n")
    if path.endswith(".lagda.md"):
        return "\n".join(re.findall(r"```agda\n(.*?)```", s, re.S))
    return s


def strip_comments(s):
    s = re.sub(r"\{-(?!#).*?-\}", lambda m: re.sub(r"[^\n]", " ", m.group(0)), s, flags=re.S)
    return re.sub(r"(^|\s)--(?!.*#-\}).*$", r"\1", s, flags=re.M)


def telescope_args(tel):
    """`{c m a : Level} (𝒯 : Theory c m a) ⦃ i : X ⦄` -> ['{c}', '{m}', '{a}', '𝒯', '⦃ i ⦄']"""
    out, i, depth = [], 0, 0
    groups = []
    start = None
    opens = {"(": ")", "{": "}", "⦃": "⦄"}
    stack = []
    for k, ch in enumerate(tel):
        if ch in opens and not stack:
            stack.append(ch)
            start = k
        elif ch in opens:
            stack.append(ch)
        elif stack and ch == opens[stack[-1]]:
            stack.pop()
            if not stack:
                groups.append((tel[start], tel[start + 1:k]))
    for kind, body in groups:
        if ":" not in body:
            names = body.split()
        else:
            names = body.split(":", 1)[0].split()
        for n in names:
            n = n.lstrip("@").strip()
            if n in ("", "_"):
                raise ValueError("anonymous module parameter")
            if kind == "(":
                out.append(n)
            elif kind == "{":
                out.append("{" + n + "}")
            else:
                out.append("⦃ " + n + " ⦄")
    return out


def header_end(lines, i):
    """Index of the line containing the `where` that ends a module header starting at i."""
    j = i
    while j < len(lines) and not re.search(r"\bwhere\s*$", lines[j]):
        j += 1
    return j


def indent(l):
    return len(l) - len(l.lstrip())


def generate(src, mod):
    base = os.path.join(src, *mod.split("."))
    path = base + ".lagda.md" if os.path.exists(base + ".lagda.md") else base + ".agda"
    code = code_of(path)
    lines = code.split("\n")
    clean = strip_comments(code).split("\n")
    new_mod = "SCT.Scratch.LossyAudit." + mod.removeprefix("SCT.")

    # options and header
    out_lines = []
    hi = next(i for i, l in enumerate(clean) if re.match(r"module\s+" + re.escape(mod) + r"\b", l))
    he = header_end(clean, hi)
    header = " ".join(clean[hi:he + 1])
    tel = re.sub(r"\bwhere\s*$", "", header.split(mod, 1)[1]).strip()
    top_args = telescope_args(tel)
    for i, l in enumerate(lines):
        if i < hi:
            l = re.sub(r"\s*--lossy-unification", "", l)
        out_lines.append(l)
    out_lines[hi] = out_lines[hi].replace(mod, new_mod, 1)

    # blocks: list of (header_line, body_indent, end_line, path, args, exported)
    checks = {}      # insert-after line index -> list of lines
    skipped = []
    compared = 0
    typed = 0

    def body_end(start, ind):
        k = start
        last = start - 1
        while k < len(clean):
            if clean[k].strip():
                if indent(clean[k]) < ind:
                    break
                last = k
            k += 1
        return last

    def walk(first, last, ind, path, args, hidden, attach=None):
        """attach = (line, indent) where checks for this block go (default: end of block)."""
        at_line, at_ind = attach or (last, ind)
        nonlocal compared, typed
        i = first
        while i <= last:
            l = clean[i]
            if not l.strip() or indent(l) != ind:
                i += 1
                continue
            s = l.strip()
            # block headers
            m = re.match(r"(private|abstract|opaque|instance|mutual)\s*$", s)
            if m:
                bi = next((k for k in range(i + 1, last + 1) if clean[k].strip()), None)
                if bi is not None and indent(clean[bi]) > ind:
                    be = body_end(bi, indent(clean[bi]))
                    h = hidden
                    if m.group(1) == "private":
                        h = "private"
                    elif m.group(1) in ("abstract", "opaque") and not hidden:
                        h = "sealed"
                    walk(bi, be, indent(clean[bi]), path, args, h, (at_line, at_ind))
                    i = be + 1
                    continue
            m = re.match(r"module\s+(" + NAME + r")(.*)$", s)
            if m and "=" not in s.split("where")[0] and not re.match(r"module\s+\S+\s*=", s):
                he2 = header_end(clean, i)
                hdr = " ".join(x.strip() for x in clean[i:he2 + 1])
                name = m.group(1)
                tel2 = re.sub(r"\bwhere\s*$", "", hdr[hdr.index(name) + len(name):]).strip()
                bi = next((k for k in range(he2 + 1, len(clean)) if clean[k].strip()), None)
                if bi is None or indent(clean[bi]) <= ind:
                    i = he2 + 1
                    continue
                be = body_end(bi, indent(clean[bi]))
                try:
                    sub_args = telescope_args(tel2)
                except ValueError:
                    skipped.append(f"module {name}: anonymous parameter")
                    i = be + 1
                    continue
                walk(bi, be, indent(clean[bi]), path + ([] if name == "_" else [name]),
                     args + sub_args, hidden)
                i = be + 1
                continue
            m = re.match(r"(" + NAME + r")\s*:(\s|$)", s)
            if m and m.group(1) not in ("field", "constructor"):
                d = m.group(1)
                # signature runs until the first line at indentation ind that is not a continuation
                k = i + 1
                while k <= last and (not clean[k].strip() or indent(clean[k]) > ind):
                    k += 1
                sig = " ".join(x.strip() for x in clean[i:k])
                T = sig.split(":", 1)[1].strip()
                end = k
                while end <= last and (not clean[end].strip() or indent(clean[end]) > ind
                                       or re.match(r"\s*" + re.escape(d) + r"(\s|$)", clean[end])):
                    end += 1
                target = "Lossy′." + ".".join(path + [d])
                if args:
                    target = "(" + target + " " + " ".join(args) + ")"
                if hidden == "private":
                    skipped.append(f"{'.'.join(path + [d])}: private")
                elif hidden == "sealed":
                    # the term is invisible downstream, but its type is not: compare types
                    pad = " " * at_ind
                    checks.setdefault(at_line, []).extend([
                        pad + "_ : " + T,
                        pad + "_ = " + target,
                    ])
                    typed += 1
                elif re.search(r"\bLevel\b|Setω|\bSet\b|\bProp\b", T):
                    skipped.append(f"{'.'.join(path + [d])}: type mentions Level/Set")
                else:
                    dd = d
                    pad = " " * at_ind
                    checks.setdefault(at_line, []).extend([
                        pad + "_ : Eqᴸ._≡_ {A = " + T + "}",
                        pad + "      " + dd + " " + target,
                        pad + "_ = Eqᴸ.refl",
                    ])
                    compared += 1
                i = end
                continue
            i += 1

    first = he + 1
    body = [k for k in range(first, len(clean)) if clean[k].strip()]
    ind0 = indent(clean[body[0]]) if body else 0
    walk(first, len(clean) - 1, ind0, [], [], False)

    # import of the lossy original right after the header
    imp = ["", "import Agda.Builtin.Equality as Eqᴸ",
           "import " + mod + (" " + " ".join(top_args) if top_args else "") + " as Lossy′", ""]
    result = []
    for k, l in enumerate(out_lines):
        result.append(l)
        if k == he:
            result.extend(imp)
        if k in checks:
            result.extend(checks[k])
    result.append("")
    result.append(f"-- Compared {compared} definitions; compared only the types of {typed} abstract/opaque ones. Not compared:")
    result.extend("--   " + x for x in skipped)
    out = os.path.join(src, "SCT", "Scratch", "LossyAudit", *mod.removeprefix("SCT.").split(".")) + ".agda"
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w", encoding="utf8", newline="\n").write("\n".join(result) + "\n")
    return out, compared, typed, skipped


if __name__ == "__main__":
    if len(sys.argv) < 3:
        sys.exit(__doc__)
    for m in sys.argv[2:]:
        out, n, t, s = generate(sys.argv[1], m)
        print(f"{m}: {n} compared, {t} types only, {len(s)} not compared -> {out}")
