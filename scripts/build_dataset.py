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
      "proof":              <a self-contained Lean FILE that ends with the target theorem
                             proved for real: the FULL dependency closure — upstream
                             lemmas/theorems included, with their original proof bodies —
                             flattened in compile order (see "proof-file assembly" below)>,
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

DEF_KINDS = {"def", "abbrev", "structure", "inductive", "class", "instance", "axiom", "opaque"}
PROOF_KINDS = {"theorem", "lemma"}
ALL_KINDS = DEF_KINDS | PROOF_KINDS

_MODIFIERS = r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+|@\[[^\]]*\]\s*)*"
KIND_RE = re.compile(r"^\s*" + _MODIFIERS + r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example|axiom|opaque)\b")
DECL_COL0_RE = re.compile(r"^" + _MODIFIERS + r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example|axiom|opaque)\b")
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)")
SECTION_RE = re.compile(r"^\s*section\b")
END_RE = re.compile(r"^\s*end\b")
VAR_RE = re.compile(r"^\s*variable\b")
PREAMBLE_RE = re.compile(r"^\s*(open|notation|local\s+notation|scoped\s+notation|infix|infixl|infixr|prefix|postfix|set_option)\b")
PRIVATE_RE = re.compile(r"^_private\..*?\.\d+\.")
# Lean identifiers admit unicode letters (ρ, σ, ...) plus primes/sub-/superscripts; use
# \w (unicode-aware) with the extra marks Lean allows so Greek-lettered names survive.
_ID_EXTRA = "'!?₀-₉₊-ₜ′″ᵢ-ᵪ"
IDENT_RE = re.compile(rf"[^\W\d][\w{_ID_EXTRA}]*(?:\.[^\W\d][\w{_ID_EXTRA}]*)*")
LEAN_BIND_RE = re.compile(r"^\s*\\lean\{([^}]*)\}\s*$")
INLINE_LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
BEGIN_RE = re.compile(r"\\begin\{(theorem|lemma|definition|proposition|corollary|sublemma)\}(?:\[([^\]]*)\])?")
END_ENV_RE = re.compile(r"\\end\{(theorem|lemma|definition|proposition|corollary|sublemma)\}")
DROP_LINE_RE = re.compile(r"^\s*\\(leanok|label|uses|lean|difficulty)\b")
USES_RE = re.compile(r"\\uses\{")
DIFF_RE = re.compile(r"^\s*\\difficulty\{([^}]*)\}\s*$")

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
            difficulty = None        # \difficulty{N}: intrinsic, tactic-only proof rating
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
                mdiff = DIFF_RE.match(line)
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
                elif mdiff:
                    # Capture \difficulty{N} while dropping it from the prose.
                    try:
                        difficulty = int(mdiff.group(1).strip())
                    except ValueError:
                        difficulty = None
                elif DROP_LINE_RE.match(line):
                    skip_braces = max(0, line.count("{") - line.count("}"))
                else:
                    body.append(line)
                i += 1
            if bindings:
                informal = "\n".join(body)
                # Keep a leading space: `\cdot\lean{BoolBLR.lift\_pm1}` must not splice
                # into the undefined TeX control word `\cdotBoolBLR...`.
                informal = INLINE_LEAN_RE.sub(lambda m: " " + m.group(1), informal)
                informal = re.sub(r"\n{3,}", "\n\n", informal).strip()
                uses = [u.strip() for u in re.sub(r"[{}]", " ", uses_raw).split(",") if u.strip()]
                for b in bindings:
                    out.setdefault(b, {"env": env, "informal": informal, "title": title,
                                       "uses": uses, "difficulty": difficulty})
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
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        if NS_RE.match(line):
            scopes.append({"kind": "ns", "name": NS_RE.match(line).group(1), "vars": []})
            i += 1
            continue
        if SECTION_RE.match(line):
            scopes.append({"kind": "sec", "name": None, "vars": []})
            i += 1
            continue
        if END_RE.match(line):
            if len(scopes) > 1:
                scopes.pop()
            i += 1
            continue
        if VAR_RE.match(line):
            j = variable_span_end(lines, i)
            scopes[-1]["vars"].append("\n".join(l.rstrip() for l in lines[i:j]))
            i = j
            continue
        if PREAMBLE_RE.match(line):
            preamble.append(line.rstrip())
            i += 1
            continue
        if DECL_COL0_RE.match(line):
            ns = ".".join(s["name"] for s in scopes if s["kind"] == "ns" and s["name"])
            vrs = [v for s in scopes for v in s["vars"]]
            decl_ctx[i] = {"namespace": ns, "variables": vrs}
        i += 1
    return preamble, decl_ctx


def variable_span_end(lines: list[str], i: int) -> int:
    """Exclusive end of the `variable` command starting at line i: a `variable` command
    continues over following indented, nonblank lines (binder lists wrap)."""
    j = i + 1
    while j < len(lines) and lines[j][:1].isspace() and lines[j].strip():
        j += 1
    return j


_BOUNDARY_KW_RE = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+|local\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|example|axiom|opaque|namespace|"
    r"section|end|open|variable|universe|set_option|notation|infix|infixl|"
    r"infixr|prefix|postfix|attribute|omit|include|mutual|macro|macro_rules|"
    r"syntax|elab|elab_rules|declare_syntax_cat)\b")


def _is_boundary(s: str) -> bool:
    """True if `s` (a source line) starts a new top-level construct.

    The declaration-keyword check tolerates leading whitespace (matching KIND_RE's own
    `^\\s*` leniency elsewhere in this file) because Lean 4 never legitimately nests a
    `theorem`/`lemma`/`def`/... keyword inside another declaration's body — a source file
    can accidentally indent one (see e.g. QuantumSingleton.lean's `symB_nondegenerate`),
    and treating it as "not a boundary" silently glues the next declaration's text onto
    the previous one's slice. The comment/attribute check stays column-0-only, since
    indented comments are common and legitimate inside a proof body.
    """
    if not s:
        return False
    if not s[0].isspace() and s.startswith(("@[", "/--", "/-", "--", "#")):
        return True
    return bool(_BOUNDARY_KW_RE.match(s.lstrip()))


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
_AUTO_NAME_RE = re.compile(r"(«|macroRules|_aux_\d|\.proof_|\.match_|\.eq_\d|\._)")


def is_real_decl_name(name: str) -> bool:
    return not _AUTO_NAME_RE.search(name)


_DECL_NAME_RE = re.compile(
    r"^\s*" + _MODIFIERS +
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\s+"
    r"([^\s\(\)\[\]\{\}⟨⟩:,;]+)")


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
            # Verify the located keyword actually declares this name. Two mismatch cases:
            # `mutual` members all share the block's start line, so the first keyword found
            # belongs to another member — scan forward for the keyword that declares this
            # name. `where`/`let rec` helpers (e.g. `foo.go`) have no keyword of their own
            # and no such line exists — those stay inside their parent's slice, so drop.
            dshort = declared_short_name(lines[kidx])
            if kind != "instance" and dshort != nname.split(".")[-1]:
                found = None
                for j in range(kidx + 1, min(kidx + 300, len(lines))):
                    mj = KIND_RE.match(lines[j])
                    if mj and declared_short_name(lines[j]) == nname.split(".")[-1]:
                        found = (j, mj.group(1))
                        break
                if found is None:
                    continue
                kidx, kind = found
            ctx = decl_ctx.get(kidx)
            if ctx is None:  # nearest preceding keyword line
                keys = [k for k in decl_ctx if k <= kidx]
                ctx = decl_ctx[max(keys)] if keys else {"namespace": "", "variables": []}
            slice_lines = lines[kidx:decl_end(lines, kidx)]
            raw[nname] = {
                "name": nname,
                "module": module,
                "kind": kind,
                "kidx": kidx,
                "namespace": ctx["namespace"],
                "variables": ctx["variables"],
                "preamble": preamble,
                "slice": slice_lines,
                "raw_deps": dd.get("deps", []),
            }

    # Second pass: resolve dependencies (normalized, TCSlib, in-index).
    # def_deps keeps its original definition-kind-only semantics (formal_statement path);
    # all_deps additionally includes theorem/lemma deps and falls back to the parent
    # declaration for constructor/projection/where-helper names (Foo.mk, foo.go, ...),
    # which never get an index entry of their own but live inside the parent's slice.
    for rec in raw.values():
        deps = set()
        alldeps = set()
        lost = set()
        for dep in rec["raw_deps"]:
            if not dep.get("module", "").startswith("TCSlib"):
                continue
            dn = normalize_name(dep["name"])
            if dn == rec["name"]:
                continue
            if dn in raw and raw[dn]["kind"] in DEF_KINDS:
                deps.add(dn)
            an = dn
            if an not in raw:
                parent = an.rsplit(".", 1)[0] if "." in an else None
                an = parent if parent in raw else None
            if an and an != rec["name"]:
                alldeps.add(an)
            elif an is None and is_real_decl_name(dn):
                lost.add(dn)
        rec["def_deps"] = sorted(deps)
        rec["all_deps"] = sorted(alldeps)
        rec["lost_deps"] = sorted(lost)
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


# ---------------------------------------------------------- proof-file assembly
#
# The `proof` field is a self-contained Lean file whose LAST declaration is the target
# theorem with its real proof. Unlike `formal_statement` (definitions only, `:= sorry`),
# it flattens the FULL dependency closure: upstream lemmas/theorems included, with their
# original proof bodies, so the final declaration elaborates.
#
# Assembly is position-aware rather than preamble-hoisting:
#   * each contributing module is parsed once into an ordered list of ITEMS —
#     declarations (with attached `@[...]` / `open ... in` / `set_option ... in` /
#     `omit ... in` prefix lines), whole `mutual ... end` blocks, and context commands
#     (universe / set_option / open / attribute / notation / macro / syntax);
#   * contributing modules are ordered by the TCSlib import DAG and items within a
#     module stay in source order — a linearization in which every reference points
#     backward, because the original library compiled that way;
#   * context commands that name TCSlib declarations are dropped unless everything they
#     reference has already been emitted (e.g. `attribute [instance] Foo.bar` for a
#     `Foo.bar` outside the closure);
#   * items are re-wrapped in their original namespace / `variable` / noncomputable-
#     section context, and namespace stubs up front make hoisted `open`s legal even
#     when the first declaration of that namespace comes later.

IMPORT_LINE_RE = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_'.«»]*)")
PREFIX_IN_RE = re.compile(r"^\s*(?:open|set_option|omit|include)\b.*\bin\s*$")
ATTR_ONLY_RE = re.compile(r"^\s*@\[[^\]]*\]\s*$")
MUTUAL_START_RE = re.compile(r"^\s*mutual\b")
END_TOKEN_RE = re.compile(r"^\s*end\b")
NONCOMP_SEC_RE = re.compile(r"^\s*noncomputable\s+section\b")
CTX_KEEP_RE = re.compile(r"^\s*(universe|set_option|open)\b")
CTX_FILTER_RE = re.compile(
    r"^\s*(?:scoped\s+|local\s+)?(attribute|macro_rules|macro|syntax|elab_rules|elab|"
    r"declare_syntax_cat|notation|infixl|infixr|infix|prefix|postfix)\b")
SEARCH_TACTIC_RE = re.compile(r"(exact\?|apply\?|rw\?|simp\?|norm_num\?|polyrith|hint\b)")
# Attributes that make a declaration usable IMPLICITLY (simp set, ext lemmas, aesop rule
# sets, ...). Such uses never appear in the source text, so the .ilean-derived dep graph
# cannot see them — these declarations are "ambient" and must ride along with any proof
# file whose import closure contains them.
AMBIENT_ATTR_RE = re.compile(
    r"@\[[^\]]*\b(simp|ext|grind|aesop|norm_num|positivity|fun_prop|measurability|"
    r"continuity|gcongr|mono|instance)\b")


def parse_module_items(lines: list[str]):
    """Ordered item model of one module: declarations, mutual blocks, context commands.

    Returns (items, by_kidx, ext_imports) where by_kidx maps a declaration-keyword line
    to its containing item (a mutual block is ONE item owning all its members' lines).
    """
    scopes = [{"kind": "sec", "name": None, "vars": [], "noncomp": False}]
    items: list[dict] = []
    by_kidx: dict[int, dict] = {}
    ext_imports: list[str] = []
    pending: list[str] = []      # @[...] / `... in` lines attached to the next item
    i, n = 0, len(lines)

    def ctx_base():
        return {
            "ns": ".".join(s["name"] for s in scopes if s["kind"] == "ns" and s["name"]),
            "vars": [v for s in scopes for v in s["vars"]],
            "noncomp": any(s["noncomp"] for s in scopes),
            "prefix": pending,
        }

    while i < n:
        line = lines[i]
        stripped = line.strip()
        if stripped.startswith(("/-", "/--")):        # skip (doc/block) comments wholesale
            depth = 0
            while i < n:
                depth += lines[i].count("/-") - lines[i].count("-/")
                i += 1
                if depth <= 0:
                    break
            continue
        if stripped == "" or stripped.startswith("--"):
            i += 1
            continue
        m_imp = IMPORT_LINE_RE.match(line)
        if m_imp:
            if not m_imp.group(1).startswith("TCSlib"):
                ext_imports.append(line.strip())
            i += 1
            continue
        if NS_RE.match(line):
            scopes.append({"kind": "ns", "name": NS_RE.match(line).group(1), "vars": [], "noncomp": False})
            i += 1
            continue
        if NONCOMP_SEC_RE.match(line):
            scopes.append({"kind": "sec", "name": None, "vars": [], "noncomp": True})
            i += 1
            continue
        if SECTION_RE.match(line):
            scopes.append({"kind": "sec", "name": None, "vars": [], "noncomp": False})
            i += 1
            continue
        if END_TOKEN_RE.match(line):
            if len(scopes) > 1:
                scopes.pop()
            i += 1
            continue
        if VAR_RE.match(line):
            j = variable_span_end(lines, i)
            scopes[-1]["vars"].append("\n".join(l.rstrip() for l in lines[i:j]))
            i = j
            continue
        if PREFIX_IN_RE.match(line) or ATTR_ONLY_RE.match(line):
            pending.append(line.rstrip())
            i += 1
            continue
        if MUTUAL_START_RE.match(line):
            j, depth = i + 1, 1
            while j < n and depth > 0:
                if MUTUAL_START_RE.match(lines[j]):
                    depth += 1
                elif END_TOKEN_RE.match(lines[j]):
                    depth -= 1
                j += 1
            item = dict(ctx_base(), type="decl", start=i, end=j)
            for k in range(i, j):
                if KIND_RE.match(lines[k]):
                    by_kidx[k] = item
            items.append(item)
            pending = []
            i = j
            continue
        if KIND_RE.match(line):
            j = decl_end(lines, i)
            item = dict(ctx_base(), type="decl", start=i, end=j)
            by_kidx[i] = item
            items.append(item)
            pending = []
            i = j
            continue
        if CTX_KEEP_RE.match(line) or CTX_FILTER_RE.match(line):
            j = decl_end(lines, i)
            # `open Foo (bar baz)` pins specific names — treat like a filtered command.
            filtered = bool(CTX_FILTER_RE.match(line)) or (
                stripped.startswith("open") and "(" in stripped)
            item = dict(ctx_base(), type="ctx_filter" if filtered else "ctx_keep",
                        start=i, end=j)
            items.append(item)
            pending = []
            i = j
            continue
        pending = []      # anything else invalidates a dangling prefix
        i += 1
    return items, by_kidx, ext_imports


def build_module_imports(modules) -> dict[str, list[str]]:
    """module -> its direct TCSlib imports."""
    imp: dict[str, list[str]] = {}
    for m in modules:
        p = module_to_lean_path(m)
        deps = []
        if p.exists():
            for line in p.read_text(encoding="utf-8", errors="ignore").splitlines():
                mm = IMPORT_LINE_RE.match(line)
                if mm and mm.group(1).startswith("TCSlib"):
                    deps.append(mm.group(1))
        imp[m] = deps
    return imp


def build_module_ranks(imp: dict[str, list[str]]) -> dict[str, int]:
    """Postorder rank over the TCSlib import DAG: imported modules rank lower."""
    rank: dict[str, int] = {}

    def visit(m, stack):
        if m in rank or m not in imp or m in stack:
            return
        stack.add(m)
        for d in imp[m]:
            visit(d, stack)
        stack.discard(m)
        rank[m] = len(rank)

    for m in imp:
        visit(m, set())
    return rank


def build_any_short_map(index) -> dict[str, str]:
    """short name -> full name, for shorts that are unambiguous across the index."""
    short, dup = {}, set()
    for nm in index:
        s = nm.split(".")[-1]
        (dup.add(s) if s in short else None)
        short[s] = nm
    for s in dup:
        short.pop(s, None)
    return short


def closure_all(seeds, index) -> set[str]:
    """Transitive closure over all_deps (definitions AND theorems/lemmas)."""
    seen: set[str] = set()
    stack = list(seeds)
    while stack:
        nm = stack.pop()
        if nm in seen:
            continue
        seen.add(nm)
        for d in index[nm]["all_deps"]:
            if d not in seen:
                stack.append(d)
    return seen


def ctx_refs_ok(text: str, ns: str, index, short_map, emitted) -> bool:
    """True if every TCSlib declaration this context command references is emitted."""
    for tok in IDENT_RE.findall(text):
        cand = None
        if tok in index:
            cand = tok
        elif ns and f"{ns}.{tok}" in index:
            cand = f"{ns}.{tok}"
        elif "." in tok:
            # Projection / constructor / field of an indexed parent (Foo.fintype), with
            # or without the surrounding namespace prefix.
            parent = tok.rsplit(".", 1)[0]
            if parent in index:
                cand = parent
            elif ns and f"{ns}.{parent}" in index:
                cand = f"{ns}.{parent}"
        elif tok in short_map:
            # Short-name fallback for dot-free tokens only: matching just the last
            # component of a dotted name would misresolve Foo.fintype to any unique
            # decl short-named `fintype`.
            cand = short_map[tok]
        if cand is not None and cand not in emitted:
            return False
    return True


def render_item(item: dict, lines: list[str]) -> str:
    """Render one item with its original context re-established.

    Declarations are wrapped in their namespace with the in-scope `variable` commands.
    ctx_keep commands (universe / set_option / open) are emitted UNWRAPPED so their
    effect persists for the rest of the file, as it did for the rest of the original
    module; an `open` that lived inside a namespace gets `open NS` prepended so names
    that resolved relative to NS still resolve. ctx_filter commands (notation /
    attribute / macro ...) keep the namespace wrapper — `scoped` declarations must sit
    inside their namespace, and their effect re-activates whenever the namespace is
    re-entered by later declarations.
    """
    body = item["prefix"] + [l.rstrip() for l in lines[item["start"]:item["end"]]]
    if item["type"] == "decl":
        block = "\n".join(item["vars"] + body)
        if item["ns"]:
            block = f"namespace {item['ns']}\n{block}\nend {item['ns']}"
        if item["noncomp"]:
            block = f"noncomputable section\n{block}\nend"
        return block
    if item["type"] == "ctx_keep":
        block = "\n".join(body)
        if item["ns"] and lines[item["start"]].lstrip().startswith("open"):
            block = f"open {item['ns']}\n{block}"
        return block
    block = "\n".join(body)
    if item["ns"]:
        block = f"namespace {item['ns']}\n{block}\nend {item['ns']}"
    return block


def build_proof(target, index, get_items, mod_rank, mod_imports, short_map, by_mod_kidx,
                by_module_names, resolve_lost, global_ns, ambient_by_module):
    """Assemble the flattened proof file for `target`.

    Returns (text, emitted_upstream_names_in_order, unresolved_dep_names).
    """
    needed = closure_all({target["name"]}, index)
    # The target module's transitive TCSlib import closure — its original environment.
    universe_mods: set[str] = set()
    stack = [target["module"]]
    while stack:
        m = stack.pop()
        if m in universe_mods:
            continue
        universe_mods.add(m)
        stack.extend(mod_imports.get(m, []))
    # Ambient declarations (implicitly usable via attributes — simp set etc.) from that
    # environment must ride along: the dep graph cannot see attribute-driven uses.
    ambient: set[str] = set()
    for m in universe_mods:
        ambient |= ambient_by_module.get(m, set())
    needed |= closure_all(ambient, index)
    lost: set[str] = set()
    for _round in range(8):
        grew = False
        # Committed search tactics (`exact?` & friends) close goals with lemmas that
        # never appear in the source text, so the reference-level dep graph cannot see
        # them. Widen conservatively: such a declaration gets every earlier declaration
        # of its own module plus everything in its module's direct TCSlib imports —
        # the region where suggestion tactics overwhelmingly find their lemma.
        widen = set()
        for nm in needed:
            rec = index[nm]
            if not SEARCH_TACTIC_RE.search("\n".join(rec["slice"])):
                continue
            mod = rec["module"]
            for n2 in by_module_names.get(mod, []):
                if index[n2]["kidx"] < rec["kidx"]:
                    widen.add(n2)
            for im in mod_imports.get(mod, []):
                widen.update(by_module_names.get(im, []))
        if not widen <= needed:
            needed |= closure_all(widen, index)
            grew = True
        # Deps the index could not resolve may still be reachable: `mutual` members the
        # dep graph did not record resolve (via the alias map) to a sibling in the same
        # block — pull that block in and re-close until stable.
        extra = set()
        lost = set()
        for nm in needed:
            for l in index[nm]["lost_deps"]:
                rep = resolve_lost(l)
                if rep is None:
                    lost.add(l)
                elif rep not in needed:
                    extra.add(rep)
        if extra:
            needed |= closure_all(extra, index)
            grew = True
        if not grew:
            break
    mods = sorted({index[nm]["module"] for nm in needed},
                  key=lambda m: (mod_rank.get(m, 10**9), m))

    # External imports: union over the target module's TRANSITIVE TCSlib import closure
    # (not just contributing modules). This reproduces byte-for-byte the environment the
    # target theorem originally elaborated in — which matters because search tactics in
    # committed proofs (`exact?`, `simp_all`) are environment-sensitive, and a blanket
    # `import Mathlib` can change their behavior (or clash with PFR's ForMathlib files).
    imports = []
    seen_imp = set()
    for m in sorted(universe_mods, key=lambda m: (mod_rank.get(m, 10**9), m)):
        _lines, _items, _bk, ext = get_items(m)
        for line in ext:
            if line not in seen_imp:
                seen_imp.add(line)
                imports.append(line)
    if not imports:
        imports = ["import Mathlib"]

    parts: list[str] = []
    emitted: set[str] = set()
    order: list[str] = []

    for m in mods:
        lines, items, by_kidx, _ext = get_items(m)
        kn = by_mod_kidx.get(m, {})                    # kidx -> declaration name
        needed_ids = set()
        item_names: dict[int, list[str]] = {}
        no_item: list[str] = []
        for k, nm in kn.items():
            it = by_kidx.get(k)
            if it is not None:
                item_names.setdefault(id(it), []).append(nm)
                if nm in needed:
                    needed_ids.add(id(it))
            elif nm in needed:
                no_item.append(nm)
        for it in items:
            if it["type"] == "decl":
                if id(it) in needed_ids:
                    parts.append(render_item(it, lines))
                    parts.append("")
                    for nm in item_names.get(id(it), []):
                        emitted.add(nm)
                        if nm in needed:
                            order.append(nm)
            elif it["type"] == "ctx_keep":
                parts.append(render_item(it, lines))
                parts.append("")
            else:  # ctx_filter
                text = "\n".join(lines[it["start"]:it["end"]])
                if ctx_refs_ok(text, it["ns"], index, short_map, emitted):
                    parts.append(render_item(it, lines))
                    parts.append("")
        for nm in no_item:                              # parser missed it — fall back
            parts.append(emit_block(index[nm], body=True))
            parts.append("")
            emitted.add(nm)
            order.append(nm)

    # Namespace stubs: `open Foo` errors when namespace Foo is not registered yet, and
    # an emitted open may fire before (or without) any declaration in that namespace.
    # Scan the assembled body's open lines and pre-register every TCSlib namespace they
    # mention. (Registering a namespace that later collides with a declaration name is
    # legal Lean — cf. `List` the namespace vs `List` the inductive.)
    body = "\n".join(parts)
    stubs = []
    seen_stub = set()
    for mline in re.finditer(r"^\s*open\s+(.+)$", body, re.MULTILINE):
        toks = mline.group(1).replace(" in", " ").split()
        for tok in toks:
            tok = tok.strip("()")
            if tok in ("scoped", "in") or not tok:
                continue
            if tok in global_ns and tok not in seen_stub:
                seen_stub.add(tok)
                stubs.append(f"namespace {tok}\nend {tok}")

    head = imports + [""] + (stubs + [""] if stubs else [])
    text = "\n".join(head) + "\n" + body.rstrip() + "\n"
    upstream = [nm for nm in order if nm != target["name"]]
    return text, upstream, sorted(lost)


def make_proof_builder(graph, index):
    """Bind the per-run caches and return build_proof(target) -> (text, upstream, lost)."""
    items_cache: dict[str, tuple] = {}

    def get_items(module):
        if module not in items_cache:
            path = module_to_lean_path(module)
            lines = (path.read_text(encoding="utf-8", errors="ignore").splitlines()
                     if path.exists() else [])
            items, by_kidx, ext = parse_module_items(lines)
            items_cache[module] = (lines, items, by_kidx, ext)
        return items_cache[module]

    mod_imports = build_module_imports(list(graph.keys()))
    mod_rank = build_module_ranks(mod_imports)

    # The dep graph is built from .ilean reference indexes and misses some declarations
    # entirely (e.g. an inductive no extended tuple ever named, or all-but-one member of
    # a `mutual` block). Overlay SYNTHETIC index entries for every declaration the item
    # parser can see that the graph didn't record, with token-scanned deps, so closures
    # can reach them. The overlay is proof-path-private: formal_statement still sees the
    # graph-derived index only.
    pindex = dict(index)
    known_kidx: dict[str, set[int]] = {}
    for nm, rec in index.items():
        known_kidx.setdefault(rec["module"], set()).add(rec["kidx"])
    synth: list[str] = []
    global_ns: set[str] = set()          # every namespace path any module ever enters
    for module in graph:
        lines, items, _bk, _ext = get_items(module)
        known = known_kidx.get(module, set())
        for it in items:
            ns = it["ns"]
            while ns:
                global_ns.add(ns)
                ns = ns.rpartition(".")[0]
            if it["type"] != "decl":
                continue
            for k in range(it["start"], it["end"]):
                mk = KIND_RE.match(lines[k])
                if k in known or not mk:
                    continue
                short = declared_short_name(lines[k])
                if not short:
                    continue
                full = f"{it['ns']}.{short}" if it["ns"] else short
                if full in pindex:
                    continue
                pindex[full] = {
                    "name": full, "module": module, "kind": mk.group(1), "kidx": k,
                    "namespace": it["ns"], "variables": it["vars"], "preamble": [],
                    "slice": lines[k:decl_end(lines, k)],
                    "def_deps": [], "all_deps": [], "lost_deps": [],
                }
                synth.append(full)

    short_map = build_any_short_map(pindex)

    imp_closure_memo: dict[str, set] = {}

    def import_closure(m):
        if m not in imp_closure_memo:
            seen: set[str] = set()
            stack = [m]
            while stack:
                x = stack.pop()
                if x in seen:
                    continue
                seen.add(x)
                stack.extend(mod_imports.get(x, []))
            imp_closure_memo[m] = seen
        return imp_closure_memo[m]

    for nm in synth:                     # token-scan bodies for TCSlib references
        rec = pindex[nm]
        deps = set()
        visible = import_closure(rec["module"])   # a decl can only reference its imports
        for tok in IDENT_RE.findall("\n".join(rec["slice"])):
            cand = tok if tok in pindex else short_map.get(tok.split(".")[-1])
            if cand and cand != nm and pindex[cand]["module"] in visible:
                deps.add(cand)
        rec["all_deps"] = sorted(deps)

    by_mod_kidx: dict[str, dict[int, str]] = {}
    by_module_names: dict[str, list[str]] = {}
    for nm, rec in pindex.items():
        by_mod_kidx.setdefault(rec["module"], {})[rec["kidx"]] = nm
        by_module_names.setdefault(rec["module"], []).append(nm)

    # Ambient declarations per module: instances, attribute-tagged decls (see
    # AMBIENT_ATTR_RE), and decls named by standalone `attribute [simp/...]` commands.
    # All of these are used IMPLICITLY (typeclass search, simp set, ...) so the
    # reference-level dep graph never records their uses.
    ambient_by_module: dict[str, set] = {}
    for module in graph:
        lines, items, _bk, _ext = get_items(module)
        kn = by_mod_kidx.get(module, {})
        amb: set[str] = set()
        for it in items:
            if it["type"] == "decl":
                for k in range(it["start"], it["end"]):
                    nm = kn.get(k)
                    if nm is None:
                        continue
                    if pindex[nm]["kind"] == "instance":
                        amb.add(nm)
                        continue
                    attr_text = "\n".join(it["prefix"] + [lines[k]])
                    if AMBIENT_ATTR_RE.search(attr_text):
                        amb.add(nm)
            elif it["type"] == "ctx_filter":
                text = "\n".join(lines[it["start"]:it["end"]])
                if text.lstrip().startswith("attribute") and AMBIENT_ATTR_RE.search(text):
                    for tok in IDENT_RE.findall(text):
                        cand = tok if tok in pindex else short_map.get(tok.split(".")[-1])
                        if cand:
                            amb.add(cand)
        if amb:
            ambient_by_module[module] = amb

    # Residual aliasing for declaration lines the synthetics could not name.
    alias: dict[str, str] = {}
    for module in graph:
        lines, items, _bk, _ext = get_items(module)
        kn = by_mod_kidx.get(module, {})
        for it in items:
            if it["type"] != "decl":
                continue
            reps = [kn[k] for k in range(it["start"], it["end"]) if k in kn]
            if not reps:
                continue
            for k in range(it["start"], it["end"]):
                if k in kn or not KIND_RE.match(lines[k]):
                    continue
                short = declared_short_name(lines[k])
                if short:
                    full = f"{it['ns']}.{short}" if it["ns"] else short
                    alias.setdefault(full, reps[0])

    def resolve_lost(name: str):
        """Progressively strip trailing components: Foo.Bar.mk -> Foo.Bar -> Foo."""
        parts = name.split(".")
        for k in range(len(parts), 0, -1):
            cand = ".".join(parts[:k])
            if cand in alias:
                return alias[cand]
            if cand in pindex:
                return cand
        return None

    def build(target):
        return build_proof(target, pindex, get_items, mod_rank, mod_imports, short_map,
                           by_mod_kidx, by_module_names, resolve_lost, global_ns,
                           ambient_by_module)

    return build


# -------------------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", default=str(DEFAULT_OUT))
    ap.add_argument("--limit", type=int, default=None, help="Only emit the first N theorems.")
    ap.add_argument("--all-def-deps", action="store_true",
                    help="Seed from ALL definition deps, not just those in the statement text.")
    ap.add_argument("--no-proof", action="store_true",
                    help="Skip the flattened `proof` field (faster, smaller output).")
    ap.add_argument("--proof-of", default=None, metavar="NAME",
                    help="Debug: write the flattened proof file for one theorem and exit.")
    ap.add_argument("--proof-out", default=None, metavar="FILE",
                    help="Where --proof-of writes the .lean file (default: stdout).")
    args = ap.parse_args()

    if not DEP_GRAPH.exists():
        print(f"ERROR: {DEP_GRAPH} not found.")
        return 1

    graph = json.load(open(DEP_GRAPH))["modules"]
    print("Indexing declarations ...")
    index = build_index(graph)
    print(f"  {len(index)} declarations indexed "
          f"({sum(1 for r in index.values() if r['kind'] in PROOF_KINDS)} theorems/lemmas).")

    proof_builder = None
    if not args.no_proof or args.proof_of:
        proof_builder = make_proof_builder(graph, index)

    if args.proof_of:
        if args.proof_of not in index:
            print(f"ERROR: {args.proof_of} not in index.")
            return 1
        text, upstream, lost = proof_builder(index[args.proof_of])
        if args.proof_out:
            Path(args.proof_out).write_text(text, encoding="utf-8")
            print(f"Wrote {args.proof_out} ({len(text.splitlines())} lines, "
                  f"{len(upstream)} upstream decls)")
        else:
            print(text)
        if lost:
            print(f"WARNING: unresolved TCSlib deps: {lost}")
        return 0

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

    # Generic (any-kind) short-name resolver for the difficulty graph, which walks the
    # blueprint's \uses edges regardless of whether they point at a definition or a
    # theorem/lemma (unlike def_short/resolve_def, which are definition-only).
    any_short = {}
    dup_any = set()
    for n in index:
        s = n.split(".")[-1]
        (dup_any.add(s) if s in any_short else None)
        any_short[s] = n
    for s in dup_any:
        any_short.pop(s, None)

    def resolve_any(u):
        if u in index:
            return u
        return any_short.get(u.split(".")[-1])

    diff_memo = {}

    def final_difficulty(name, stack):
        """Max-difficulty-path aggregation, starting from the leaves of the \\uses graph:
        a node's final difficulty is its own intrinsic (tactic-only) \\difficulty plus the
        largest final difficulty among its prerequisites. Definitions default to 0 (they
        never carry their own \\difficulty); a theorem/lemma with no rating yet makes the
        result unknown (None), and unknown propagates to anything depending on it."""
        if name in diff_memo:
            return diff_memo[name]
        if name in stack:
            # Dependency-cycle back-edge: a cycle edge can never be a genuine
            # prerequisite ordering (it is a blueprint \uses mistake), so contribute
            # nothing rather than poisoning every downstream aggregate with unknown.
            return 0
        stack.add(name)
        entry = lookup(name)
        kind = index[name]["kind"] if name in index else None
        own = entry.get("difficulty") if entry else None
        if own is None and kind in DEF_KINDS:
            own = 0
        best = 0
        unknown = own is None
        for u in (entry.get("uses", []) if entry else []):
            dep = resolve_any(u)
            if not dep or dep == name:
                continue
            d = final_difficulty(dep, stack)
            if d is None:
                unknown = True
            elif d > best:
                best = d
        stack.discard(name)
        result = None if unknown else own + best
        diff_memo[name] = result
        return result

    # ---- breadth-aware difficulty: discounted sum of vertex-disjoint heavy chains ----
    # The plain `difficulty` is the heaviest path (critical path) through the \uses
    # graph. That ignores breadth: a theorem resting on several INDEPENDENT hard chains
    # is harder than one resting on a single chain of the same height. Here we greedily
    # peel vertex-disjoint heavy chains (Menger-style: peeling stops by itself once the
    # residual graph has no positive-weight leaf→target path, i.e. at the min cut) and
    # combine them with a geometric discount so breadth is sublinear, never additive:
    #     D = own + w1 + α·w2 + α²·w3 + ...        (α = 0.5, at most 8 chains)
    # Chains must be disjoint only on POSITIVELY-weighted nodes — zero-weight
    # definitions are plumbing shared by every chain and must not cap parallelism.
    BREADTH_ALPHA = 0.5
    BREADTH_MAX_CHAINS = 8

    def intrinsic(name):
        e = lookup(name)
        own = e.get("difficulty") if e else None
        if own is None and (index[name]["kind"] if name in index else None) in DEF_KINDS:
            own = 0
        return own

    def uses_deps(name):
        e = lookup(name)
        out = []
        for u in (e.get("uses", []) if e else []):
            dep = resolve_any(u)
            if dep and dep != name:
                out.append(dep)
        return out

    def breadth_difficulty(name):
        base = final_difficulty(name, set())
        if base is None:
            return None                     # unknown somewhere upstream: stay unknown
        removed: set[str] = set()
        total = float(intrinsic(name) or 0)
        disc = 1.0
        for _ in range(BREADTH_MAX_CHAINS):
            memo_p: dict[str, tuple] = {}

            def best(n, stack):
                if n in memo_p:
                    return memo_p[n]
                if n in stack:
                    return (0.0, ())        # cycle back-edge: contributes nothing
                stack.add(n)
                bw, bp = 0.0, ()
                for d in uses_deps(n):
                    if d in removed:
                        continue
                    w, p = best(d, stack)
                    w2 = w + (intrinsic(d) or 0)
                    if w2 > bw:
                        bw, bp = w2, p + (d,)
                stack.discard(n)
                memo_p[n] = (bw, bp)
                return memo_p[n]

            w, path = best(name, set())
            if w <= 0:
                break
            total += disc * w
            disc *= BREADTH_ALPHA
            for d in path:
                if (intrinsic(d) or 0) > 0:
                    removed.add(d)
        return round(total, 1)

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
    proof_lines_total = proof_lines_max = n_proof_unresolved = 0
    with open(out_path, "w", encoding="utf-8") as f:
        for name in targets:
            rec = index[name]
            info = lookup(name)
            if info is None:
                n_missing += 1
                continue
            formal, ordered = build_formal(rec, index, args.all_def_deps)
            total_defs += len(ordered)

            proof_text = proof_upstream = proof_lost = None
            if proof_builder is not None:
                proof_text, proof_upstream, proof_lost = proof_builder(rec)
                nl = proof_text.count("\n")
                proof_lines_total += nl
                proof_lines_max = max(proof_lines_max, nl)
                n_proof_unresolved += bool(proof_lost)

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
                # A difficulty rating only makes sense for a finished proof: null it
                # when the flattened proof (target or any upstream) still has `sorry`.
                "difficulty": (None if proof_text is not None and "sorry" in proof_text
                               else final_difficulty(name, set())),
                # Breadth-aware variant: discounted sum of vertex-disjoint heavy chains
                # (first chain = the critical path above, extra parallel chains at
                # α, α², ... — see breadth_difficulty).
                "difficulty_breadth": (None if proof_text is not None and "sorry" in proof_text
                                       else breadth_difficulty(name)),
            }
            if proof_builder is not None:
                record["proof"] = proof_text
                record["proof_upstream_decls"] = proof_upstream
                record["n_proof_upstream_decls"] = len(proof_upstream)
                record["proof_unresolved_deps"] = proof_lost
                # False when the flattened file still contains `sorry` — i.e. the
                # library itself has not finished this proof (or an upstream one).
                record["proof_complete"] = "sorry" not in proof_text
            f.write(json.dumps(record, ensure_ascii=False) + "\n")
            n_written += 1

    print()
    print(f"Wrote {n_written} records -> {out_path.relative_to(BASE)}")
    print(f"Theorems without a blueprint informal statement (skipped): {n_missing}")
    if n_written:
        print(f"Avg upstream definitions per theorem: {total_defs / n_written:.1f}")
    if n_written and proof_builder is not None:
        print(f"Proof files: avg {proof_lines_total / n_written:.0f} lines, "
              f"max {proof_lines_max} lines; "
              f"{n_proof_unresolved} records with unresolved deps")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
