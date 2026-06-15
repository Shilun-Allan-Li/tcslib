"""
Build a JSONL dataset of TCSlib theorem statements (no LLM involved).

For every theorem / lemma in dep_graph.json this emits one record:

    {
      "id":                 <fully-qualified Lean name>,
      "informal_statement": <self-contained prose: first the informal definitions of every
                             term the statement uses (pulled from the upstream blueprint
                             entries, in dependency order), then the title-folded claim>,
      "statement_informal": <just the title-folded claim, without the definitions block>,
      "definitions":        <[{id,title,informal}] for each inlined term definition>,
      "formal_statement":   <a self-contained Lean snippet: `import Mathlib`, the upstream
                             DEFINITIONS the statement depends on (full, in dependency
                             order), then the theorem statement with its proof replaced by
                             `sorry`>,
      ...metadata...
    }

How the formal statement is assembled
-------------------------------------
* The target theorem is reduced to its **signature** — everything up to the top-level
  `:=` that begins the proof (depth-aware, so default-argument `:=` inside binders are
  ignored) — and `:= sorry` is appended.
* Seed definitions = the declarations that appear **in the statement text** and resolve
  to a TCSlib definition (def / abbrev / structure / inductive / class / instance).
  This realises "keep only the upstream definitions *from the statement*".
* The dependency walk then takes the transitive closure of those seeds **over
  definition-kind nodes only** — proof-only lemmas/theorems are never pulled in, so the
  chain "does not include extra theorems not critical to the statement".
* Definitions are emitted full (a definition's body is what makes the statement
  typecheck), topologically ordered (dependencies first), each wrapped in its original
  namespace with the `variable` lines that were in scope.

The result imports only Mathlib. It is a best-effort standalone file: the dependency
content is exact, but exotic `open`/notation/`variable` context from the original modules
may occasionally need manual touch-up to fully compile.

Usage:
    python3 scripts/build_dataset.py                       # -> dataset/tcslib_theorems.jsonl
    python3 scripts/build_dataset.py --out FILE --limit N
    python3 scripts/build_dataset.py --all-def-deps        # seed from ALL def-deps, not just
                                                            # those textually in the statement
"""

import argparse
import json
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
DEP_GRAPH = BASE / "dep_graph.json"
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
DEFAULT_OUT = BASE / "dataset" / "tcslib_theorems.jsonl"

DEF_KINDS = {"def", "abbrev", "structure", "inductive", "class", "instance"}
PROOF_KINDS = {"theorem", "lemma"}
ALL_KINDS = DEF_KINDS | PROOF_KINDS

_MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+|@\[[^\]]*\]\s*)*"
KIND_RE = re.compile(r"^\s*" + _MODIFIERS + r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\b")
DECL_COL0_RE = re.compile(r"^" + _MODIFIERS + r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example)\b")
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
SECTION_RE = re.compile(r"^\s*section\b")
END_RE = re.compile(r"^\s*end\b")
VAR_RE = re.compile(r"^\s*variable\b")
PREAMBLE_RE = re.compile(r"^\s*(open|notation|local\s+notation|scoped\s+notation|infix|infixl|infixr|prefix|postfix|set_option)\b")
PRIVATE_RE = re.compile(r"^_private\..*?\.\d+\.")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")
LEAN_BIND_RE = re.compile(r"^\s*\\lean\{([^}]*)\}\s*$")
INLINE_LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
BEGIN_RE = re.compile(r"\\begin\{(theorem|lemma|definition|proposition|corollary|sublemma)\}(?:\[([^\]]*)\])?")
END_ENV_RE = re.compile(r"\\end\{(theorem|lemma|definition|proposition|corollary|sublemma)\}")
DROP_LINE_RE = re.compile(r"^\s*\\(leanok|label|uses|lean)\b")
USES_RE = re.compile(r"\\uses\{")

_OPEN_DELIM = set("([{⟨")
_CLOSE_DELIM = set(")]}⟩")


def normalize_name(name: str) -> str:
    return PRIVATE_RE.sub("", name)


def module_to_lean_path(module: str) -> Path:
    rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else module
    return BASE / "TCSlib" / (rel.replace(".", "/") + ".lean")


# --------------------------------------------------------------------- blueprint

def parse_blueprint() -> dict[str, dict]:
    """binding \\lean name -> {informal, title} for every blueprint environment."""
    out: dict[str, dict] = {}
    for tex in sorted(CHAPTER_DIR.rglob("*.tex")):
        lines = tex.read_text(encoding="utf-8", errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            mb = BEGIN_RE.search(lines[i])
            if not mb:
                i += 1
                continue
            env = mb.group(1)
            title = mb.group(2) or ""
            bindings = []
            body = []
            uses_raw = ""
            skip_braces = 0   # >0 while inside a still-open dropped macro
            cap_uses = 0      # >0 while capturing a (possibly multi-line) \uses{...}
            i += 1
            while i < len(lines) and not END_ENV_RE.search(lines[i]):
                line = lines[i]
                if cap_uses > 0:
                    uses_raw += " " + line
                    cap_uses += line.count("{") - line.count("}")
                    i += 1
                    continue
                if skip_braces > 0:
                    skip_braces += line.count("{") - line.count("}")
                    i += 1
                    continue
                mbind = LEAN_BIND_RE.match(line)
                mu = USES_RE.search(line)
                if mbind:
                    # A standalone \lean{...} line binds the environment to a declaration.
                    # Environments may group several (e.g. boolToSign_{sq,not,true}); each
                    # such name is documented by this same prose.
                    for part in mbind.group(1).split(","):
                        part = part.strip()
                        if part and not part.startswith("["):
                            bindings.append(part)
                elif mu:
                    # Capture \uses{...} (the blueprint dependency edges) while dropping it
                    # from the prose; handle a multi-line argument list.
                    rest = line[mu.end() - 1:]
                    uses_raw += rest
                    cap_uses = max(0, rest.count("{") - rest.count("}"))
                elif DROP_LINE_RE.match(line):
                    skip_braces = max(0, line.count("{") - line.count("}"))
                else:
                    body.append(line)
                i += 1
            if bindings:
                informal = "\n".join(body)
                informal = INLINE_LEAN_RE.sub(lambda m: m.group(1), informal)
                informal = re.sub(r"\n{3,}", "\n\n", informal).strip()
                uses = [u.strip() for u in re.sub(r"[{}]", " ", uses_raw).split(",") if u.strip()]
                for b in bindings:
                    out.setdefault(b, {"env": env, "informal": informal, "title": title, "uses": uses})
            i += 1
    return out


# ------------------------------------------------------------------ source model

def parse_file_context(lines: list[str]):
    """Return (preamble_lines, decl_ctx) for one source file.

    decl_ctx maps a 0-indexed declaration-keyword line to {namespace, variables} — the
    namespace path and the `variable` lines in scope at that declaration.
    """
    scopes = [{"kind": "sec", "name": None, "vars": []}]  # base file scope
    preamble: list[str] = []
    decl_ctx: dict[int, dict] = {}
    for i, line in enumerate(lines):
        if NS_RE.match(line):
            scopes.append({"kind": "ns", "name": NS_RE.match(line).group(1), "vars": []})
            continue
        if SECTION_RE.match(line):
            scopes.append({"kind": "sec", "name": None, "vars": []})
            continue
        if END_RE.match(line):
            if len(scopes) > 1:
                scopes.pop()
            continue
        if VAR_RE.match(line):
            scopes[-1]["vars"].append(line.rstrip())
            continue
        if PREAMBLE_RE.match(line):
            preamble.append(line.rstrip())
            continue
        if DECL_COL0_RE.match(line):
            ns = ".".join(s["name"] for s in scopes if s["kind"] == "ns" and s["name"])
            vrs = [v for s in scopes for v in s["vars"]]
            decl_ctx[i] = {"namespace": ns, "variables": vrs}
    return preamble, decl_ctx


_BOUNDARY_KW_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example|namespace|"
    r"section|end|open|variable|universe|set_option|notation|infix|infixl|"
    r"infixr|prefix|postfix|attribute)\b")


def _is_boundary(s: str) -> bool:
    """True if `s` (a source line) starts a new top-level construct at column 0."""
    if not s or s[0].isspace():
        return False
    if s.startswith(("@[", "/--", "/-", "--")):
        return True
    return bool(_BOUNDARY_KW_RE.match(s))


def find_keyword_idx(lines: list[str], start: int):
    """0-indexed line of the declaration keyword at/after the dep_graph start line.

    dep_graph start lines point at the declaration or its (possibly long) docstring, so we
    take the first real keyword at/after that line — which is this declaration's own.
    """
    lo = max(0, start - 1)
    for i in range(lo, len(lines)):
        m = KIND_RE.match(lines[i])
        if m:
            return i, m.group(1)
    return None, None


# Lean elaboration emits helper declarations (macro rules, match/proof terms) that are not
# real statements and must never enter the dataset.
_AUTO_NAME_RE = re.compile(r"(«|macroRules|_aux_|\.proof_|\.match_|\.eq_\d|\._)")


def is_real_decl_name(name: str) -> bool:
    return not _AUTO_NAME_RE.search(name)


_DECL_NAME_RE = re.compile(
    r"^\s*" + _MODIFIERS +
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'!?.]*)")


def declared_short_name(line: str):
    m = _DECL_NAME_RE.match(line)
    return m.group(1).split(".")[-1] if m else None


def decl_end(lines: list[str], kidx: int) -> int:
    """Exclusive end line of the declaration that starts at `kidx`, read from source.

    Spans the full body: stops at the next column-0 top-level construct, then trims
    trailing blank lines. This is authoritative where dep_graph's endLine undershoots.
    """
    i = kidx + 1
    while i < len(lines) and not _is_boundary(lines[i]):
        i += 1
    while i - 1 > kidx and lines[i - 1].strip() == "":
        i -= 1
    return i


def split_signature(text: str) -> str:
    """Everything up to the first top-level `:=` (proof separator), depth-aware."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c in _OPEN_DELIM:
            depth += 1
        elif c in _CLOSE_DELIM:
            depth -= 1
        elif depth == 0 and c == ":" and i + 1 < n and text[i + 1] == "=":
            return text[:i].rstrip()
        i += 1
    return text.rstrip()


# ------------------------------------------------------------------- index build

def build_index(graph: dict):
    """Return decl_index: normalized name -> record with kind, location, context, def-deps."""
    file_cache: dict[str, tuple] = {}   # module -> (lines, preamble, decl_ctx)
    raw: dict[str, dict] = {}

    def load(module):
        if module not in file_cache:
            path = module_to_lean_path(module)
            if not path.exists():
                file_cache[module] = (None, [], {})
            else:
                lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
                preamble, decl_ctx = parse_file_context(lines)
                file_cache[module] = (lines, preamble, decl_ctx)
        return file_cache[module]

    # First pass: locate, classify, slice.
    for module, mdata in graph.items():
        lines, preamble, decl_ctx = load(module)
        if lines is None:
            continue
        for name, dd in mdata["declarations"].items():
            kidx, kind = find_keyword_idx(lines, dd["startLine"])
            if kind not in ALL_KINDS:
                continue
            nname = normalize_name(name)
            if not is_real_decl_name(nname) or nname in raw:
                continue  # skip elaborator-generated helpers; first name wins
            # Verify the located keyword actually declares this name. `where`/`let rec`
            # helpers (e.g. `foo.go`) have no keyword of their own, so the search lands on
            # an unrelated later declaration — those are already inside their parent's
            # slice and never referenced externally, so drop them.
            dshort = declared_short_name(lines[kidx])
            if kind != "instance" and dshort != nname.split(".")[-1]:
                continue
            ctx = decl_ctx.get(kidx)
            if ctx is None:  # nearest preceding keyword line
                keys = [k for k in decl_ctx if k <= kidx]
                ctx = decl_ctx[max(keys)] if keys else {"namespace": "", "variables": []}
            slice_lines = lines[kidx:decl_end(lines, kidx)]
            raw[nname] = {
                "name": nname,
                "module": module,
                "kind": kind,
                "namespace": ctx["namespace"],
                "variables": ctx["variables"],
                "preamble": preamble,
                "slice": slice_lines,
                "raw_deps": dd.get("deps", []),
            }

    # Second pass: resolve definition-kind dependencies (normalized, TCSlib, in-index).
    for rec in raw.values():
        deps = set()
        for dep in rec["raw_deps"]:
            if not dep.get("module", "").startswith("TCSlib"):
                continue
            dn = normalize_name(dep["name"])
            if dn != rec["name"] and dn in raw and raw[dn]["kind"] in DEF_KINDS:
                deps.add(dn)
        rec["def_deps"] = sorted(deps)
        del rec["raw_deps"]
    return raw


# --------------------------------------------------------------- formal assembly

def statement_text(rec) -> str:
    return split_signature("\n".join(rec["slice"]))


def seed_defs(rec, index, all_def_deps: bool) -> list[str]:
    """Definitions to seed the walk from: by default, those named in the statement."""
    defs = [d for d in rec["def_deps"]]  # already def-kind, TCSlib, in-index
    if all_def_deps:
        return defs
    sig = statement_text(rec)
    shorts = {tok.split(".")[-1] for tok in IDENT_RE.findall(sig)}
    return [d for d in defs if index[d]["name"].split(".")[-1] in shorts]


def closure(seeds, index) -> set[str]:
    seen: set[str] = set()
    stack = list(seeds)
    while stack:
        n = stack.pop()
        if n in seen:
            continue
        seen.add(n)
        for d in index[n]["def_deps"]:
            if d not in seen:
                stack.append(d)
    return seen


def toposort(names: set[str], index) -> list[str]:
    """Dependencies before dependents; ties broken by (module, start) for determinism."""
    order_key = {n: (index[n]["module"], index[n]["slice"][0] if index[n]["slice"] else "") for n in names}
    remaining = set(names)
    emitted: list[str] = []
    placed: set[str] = set()
    while remaining:
        ready = sorted(
            (n for n in remaining if all(d in placed or d not in names for d in index[n]["def_deps"])),
            key=lambda n: order_key[n],
        )
        if not ready:  # dependency cycle — emit the rest deterministically
            ready = sorted(remaining, key=lambda n: order_key[n])
        for n in ready:
            emitted.append(n)
            placed.add(n)
            remaining.discard(n)
    return emitted


def emit_block(rec, body: bool) -> str:
    inner = list(rec["variables"])
    if body:
        inner += rec["slice"]
    else:
        inner += [statement_text(rec) + " := sorry"]
    block = "\n".join(inner)
    ns = rec["namespace"]
    if ns:
        return f"namespace {ns}\n{block}\nend {ns}"
    return block


def build_formal(target, index, all_def_deps: bool):
    seeds = seed_defs(target, index, all_def_deps)
    deps = closure(seeds, index)
    ordered = toposort(deps, index)

    # Preamble: union of open/notation/set_option lines from all contributing modules.
    preamble: list[str] = []
    seen_pre = set()
    for n in ordered + [target["name"]]:
        for line in index[n]["preamble"] if n in index else target["preamble"]:
            if line not in seen_pre:
                seen_pre.add(line)
                preamble.append(line)

    parts = ["import Mathlib", ""]
    if preamble:
        parts += preamble + [""]
    for n in ordered:
        parts.append(emit_block(index[n], body=True))
        parts.append("")
    parts.append(emit_block(target, body=False))
    return "\n".join(parts).rstrip() + "\n", ordered


# -------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    ap.add_argument("--limit", type=int, default=None, help="Only emit the first N theorems.")
    ap.add_argument("--all-def-deps", action="store_true",
                    help="Seed from ALL definition deps, not just those in the statement text.")
    args = ap.parse_args()

    if not DEP_GRAPH.exists():
        print(f"ERROR: {DEP_GRAPH} not found.")
        return 1

    graph = json.load(open(DEP_GRAPH))["modules"]
    print("Indexing declarations ...")
    index = build_index(graph)
    print(f"  {len(index)} declarations indexed "
          f"({sum(1 for r in index.values() if r['kind'] in PROOF_KINDS)} theorems/lemmas).")

    print("Parsing blueprint ...")
    informal = parse_blueprint()
    # Some pre-existing chapters reference declarations by short (unqualified) name; allow
    # a short-name fallback when it is unambiguous.
    short_counts: dict[str, int] = {}
    for k in informal:
        short_counts[k.split(".")[-1]] = short_counts.get(k.split(".")[-1], 0) + 1
    informal_short = {k.split(".")[-1]: v for k, v in informal.items()
                      if short_counts[k.split(".")[-1]] == 1}
    print(f"  {len(informal)} blueprint entries.")

    def lookup(name):
        return informal.get(name) or informal_short.get(name.split(".")[-1])

    # Resolve a blueprint \uses name to an indexed definition (handles short names and the
    # notation case where the statement text hides the underlying def, e.g. χ_[…] -> chiS).
    def_short = {}
    dup_short = set()
    for n, r in index.items():
        if r["kind"] in DEF_KINDS:
            s = n.split(".")[-1]
            (dup_short.add(s) if s in def_short else None)
            def_short[s] = n
    for s in dup_short:
        def_short.pop(s, None)

    def resolve_def(u):
        if u in index and index[u]["kind"] in DEF_KINDS:
            return u
        return def_short.get(u.split(".")[-1])

    def compose(entry):
        """Fold the [title] into the prose so the text reads as a statement."""
        t = (entry.get("title") or "").strip()
        b = (entry.get("informal") or "").strip()
        if t and b:
            sep = " " if t.endswith((".", ":", "?", "!")) else ". "
            return f"{t}{sep}{b}"
        return b or t

    def definition_terms(name, entry, formal_ordered):
        """Ordered definitions that the statement uses: the formal def-closure plus any
        \\uses{} definitions (catches notation-hidden terms), each closed and topo-sorted."""
        defset = set(formal_ordered)
        for u in entry.get("uses", []):
            r = resolve_def(u)
            if r:
                defset |= closure({r}, index)
        return toposort(defset, index)

    targets = sorted(n for n, r in index.items() if r["kind"] in PROOF_KINDS)
    if args.limit:
        targets = targets[: args.limit]

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    n_written = n_missing = 0
    total_defs = 0
    with open(out_path, "w", encoding="utf-8") as f:
        for name in targets:
            rec = index[name]
            info = lookup(name)
            if info is None:
                n_missing += 1
                continue
            formal, ordered = build_formal(rec, index, args.all_def_deps)
            total_defs += len(ordered)

            # Self-contained informal statement: define each term it uses (from the same
            # blueprint), then state the (title-folded) claim.
            definitions = []
            for d in definition_terms(name, info, ordered):
                de = lookup(d)
                if de and (de.get("informal") or de.get("title")):
                    definitions.append({"id": d, "title": de.get("title", ""),
                                        "informal": de.get("informal", "")})
            stmt = compose(info)
            if definitions:
                defs_block = "\n".join(f"- {compose(d)}" for d in definitions)
                informal_statement = f"Definitions:\n{defs_block}\n\nStatement: {stmt}"
            else:
                informal_statement = stmt

            record = {
                "id": name,
                "informal_statement": informal_statement,
                "formal_statement": formal,
                "lean_name": name,
                "title": info["title"],
                "statement_informal": stmt,
                "definitions": definitions,
                "source_module": rec["module"],
                "kind": rec["kind"],
                "upstream_defs": ordered,
                "n_upstream_defs": len(ordered),
            }
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
            n_written += 1

    print()
    print(f"Wrote {n_written} records -> {out_path.relative_to(BASE)}")
    print(f"Theorems without a blueprint informal statement (skipped): {n_missing}")
    if n_written:
        print(f"Avg upstream definitions per theorem: {total_defs / n_written:.1f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
