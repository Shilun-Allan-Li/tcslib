"""
Build a JSONL dataset of TCSlib theorem statements (no LLM involved).

For every theorem / lemma in dep_graph.json this emits one record:

    {
      "id":                 <fully-qualified Lean name>,
      "informal_statement": <when the blueprint entry cites a reference document
                             (\\proofsource / \\statementsource): the cited passage,
                             verbatim from blueprint/src/references/<doc>.md.  Otherwise
                             prose written from the Lean: first the informal definitions
                             of every term the statement uses (pulled from the upstream
                             blueprint entries, in dependency order), then the
                             title-folded claim, then the informalized account of the
                             proof when references/informalized/<name>.md holds one.
                             See scripts/informal_sources.py>,
      "informal_source":    <"citation" or "lean": which of the two the above is>,
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
import gzip
import importlib.util
import json
import re
import shutil
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
PREAMBLE_RE = re.compile(r"^\s*(open|notation|local\s+notation|scoped\s+notation|infix|infixl|infixr|prefix|postfix|set_option|universe)\b")
#: `open Foo in` / `set_option ... in` / `omit ... in` and a standalone `@[...]` line
#: belong to the NEXT declaration, not to the file: they are kept as that declaration's
#: prefix and emitted right in front of it.
PREFIX_LINE_RE = re.compile(r"^\s*(?:(?:open|set_option|omit|include)\b.*\bin\s*$|@\[[^\]]*\]\s*$)")
NOTATION_LINE_RE = re.compile(r"^\s*(notation|local\s+notation|scoped\s+notation|infix|infixl|infixr|prefix|postfix)\b")
PRIVATE_RE = re.compile(r"^_private\..*?\.\d+\.")
# Lean identifiers admit unicode letters (ρ, σ, ...) plus primes/sub-/superscripts; use
# \w (unicode-aware) with the extra marks Lean allows so Greek-lettered names survive.
_ID_EXTRA = "'!?₀-₉₊-ₜ′″ᵢ-ᵪ"
IDENT_RE = re.compile(rf"[^\W\d][\w{_ID_EXTRA}]*(?:\.[^\W\d][\w{_ID_EXTRA}]*)*")
LEAN_BIND_RE = re.compile(r"^\s*\\lean\{([^}]*)\}\s*$")
INLINE_LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
BEGIN_RE = re.compile(r"\\begin\{(theorem|lemma|definition|proposition|corollary|sublemma)\}")
END_ENV_RE = re.compile(r"\\end\{(theorem|lemma|definition|proposition|corollary|sublemma)\}")


def env_title(line: str, pos: int) -> str:
    r"""The ``[...]`` title of a blueprint environment whose ``\begin`` ends at ``pos``.

    A plain ``\[([^\]]*)\]`` stops at the first ``]``, which truncates every title that
    holds a bracket: ``[{The $\mathrm{AC}^0[p]$ gate set}]`` arrived as
    ``{The $\mathrm{AC}^0[p`` -- an unbalanced brace and an unclosed ``$`` that then
    broke math rendering for the whole record downstream. Authors already guard such
    titles with the braces LaTeX itself needs, so track brace depth, ignore any ``]``
    sitting inside a group, and peel the guard back off.
    """
    if pos >= len(line) or line[pos] != "[":
        return ""
    depth = 0
    i = pos + 1
    while i < len(line):
        c = line[i]
        if c == "\\":               # an escaped character never delimits
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        elif c == "]" and depth <= 0:
            return _unguard(line[pos + 1:i].strip())
        i += 1
    return ""                       # unterminated on this line: no title, as before


def _unguard(title: str) -> str:
    """Drop the outer brace group, but only when it wraps the whole title."""
    if not (title.startswith("{") and title.endswith("}")):
        return title
    depth = 0
    for ch in title[:-1]:
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return title        # {a} b: the group closes early, keep as is
    return title[1:-1]


DROP_LINE_RE = re.compile(
    r"^\s*\\(leanok|label|uses|lean|difficulty|proofsource|statementsource|proofstep)\b(.*)$"
)
#: How many brace groups each dropped macro takes. `\proofstep` writes its four
#: arguments on the lines *after* the macro name, so counting braces on the macro
#: line alone stops the skip immediately and spills the arguments into the prose.
DROP_MACRO_ARITY = {
    "leanok": 0,
    "label": 1,
    "uses": 1,
    "lean": 1,
    "difficulty": 1,
    "proofsource": 2,
    "statementsource": 2,
    "proofstep": 4,
}
USES_RE = re.compile(r"\\uses\{")
DIFF_RE = re.compile(r"^\s*\\difficulty\{([^}]*)\}\s*$")

def _informal_sources():
    """scripts/informal_sources.py, loaded by path: it imports the `proofmatch` package,
    which `scripts/proofmatch.py` shadows whenever this script runs from scripts/."""
    spec = importlib.util.spec_from_file_location(
        "informal_sources", Path(__file__).resolve().parent / "informal_sources.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

_OPEN_DELIM = set("([{⟨")
_CLOSE_DELIM = set(")]}⟩")


def consume_macro_args(text: str, pending: int, depth: int) -> tuple[int, int]:
    """Eat `pending` brace groups out of `text`, resuming at brace nesting `depth`.

    Blueprint metadata macros may put their arguments on the lines that follow the
    macro name, so dropping them from the prose is a multi-line job: this returns
    the arguments and nesting still outstanding once `text` is exhausted.
    """
    for ch in text:
        if depth:
            depth += (ch == "{") - (ch == "}")
            if not depth:
                pending -= 1
        elif not pending:
            break
        elif ch == "{":
            depth = 1
    return pending, depth


def module_matches(module: str, wanted) -> bool:
    """`TCSlib.A.B` matches `TCSlib.A.B`, `A.B`, `B` (dotted suffix) or `A` (a prefix: every
    module under that area)."""
    for w in wanted:
        w = w.strip()
        if not w:
            continue
        full = w if w.startswith("TCSlib.") else "TCSlib." + w
        if module == full or module.endswith("." + w) or module.startswith(full + "."):
            return True
    return False


def normalize_name(name: str) -> str:
    return PRIVATE_RE.sub("", name)


def _squash(text: str) -> str:
    return re.sub(r"[^a-z0-9]", "", text.lower())


def _squash_prose(text: str) -> str:
    """Squash for comparing two renderings of the same sentence.

    A blueprint title and the docstring summary it was taken from differ only in
    markup -- `$G$` in one, `\\texttt{G}` in the other -- so control words are
    dropped before the comparison.
    """
    return _squash(re.sub(r"\\[a-zA-Z]+", " ", text))


def is_name_title(title: str, lean_name: str) -> bool:
    """True when a blueprint ``[title]`` says nothing beyond the Lean name itself."""
    bare = title.replace("\\_", "_").replace("\\", "").strip()
    short = lean_name.split(".")[-1]
    return _squash(bare) in (_squash(lean_name), _squash(short))


def module_to_lean_path(module: str) -> Path:
    rel = module[len("TCSlib."):] if module.startswith("TCSlib.") else module
    return BASE / "TCSlib" / (rel.replace(".", "/") + ".lean")


def display_output_path(path: Path, base: Path = BASE) -> str:
    """Prefer a repository-relative path, but support explicit external outputs."""
    try:
        return str(path.relative_to(base))
    except ValueError:
        return str(path)


# --------------------------------------------------------------------- blueprint

def parse_blueprint(chapter_dir: Path = CHAPTER_DIR) -> dict[str, dict]:
    """binding \\lean name -> {informal, title} for every blueprint environment."""
    out: dict[str, dict] = {}
    for tex in sorted(chapter_dir.rglob("*.tex")):
        lines = tex.read_text(encoding="utf-8", errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            mb = BEGIN_RE.search(lines[i])
            if not mb:
                i += 1
                continue
            env = mb.group(1)
            title = env_title(lines[i], mb.end())
            bindings = []
            body = []
            uses_raw = ""
            difficulty = None        # \difficulty{N}: intrinsic, tactic-only proof rating
            skip_braces = 0   # >0 while inside a still-open dropped macro
            skip_args = 0     # dropped-macro arguments still to be eaten
            cap_uses = 0      # >0 while capturing a (possibly multi-line) \uses{...}
            i += 1
            while i < len(lines) and not END_ENV_RE.search(lines[i]):
                line = lines[i]
                if cap_uses > 0:
                    uses_raw += " " + line
                    cap_uses += line.count("{") - line.count("}")
                    i += 1
                    continue
                if skip_args > 0 or skip_braces > 0:
                    skip_args, skip_braces = consume_macro_args(
                        line, skip_args, skip_braces
                    )
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
                elif mdrop := DROP_LINE_RE.match(line):
                    skip_args, skip_braces = consume_macro_args(
                        mdrop.group(2), DROP_MACRO_ARITY[mdrop.group(1)], 0
                    )
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
    """Return (preamble_lines, decl_ctx, ext_imports) for one source file.

    decl_ctx maps a 0-indexed declaration-keyword line to {namespace, variables, prefix}
    — the namespace path, the `variable` lines in scope at that declaration, and the
    `... in` / `@[...]` lines written directly in front of it.  preamble_lines are
    (namespace, line) pairs for the file's open/notation/set_option/universe commands,
    the namespace being the one the command was written in (an `open Foo` inside
    `namespace A` means `A.Foo` when that exists; a `scoped notation` only lives inside
    its namespace).  ext_imports are the file's non-TCSlib `import` lines (the
    environment its statements elaborated in).
    """
    scopes = [{"kind": "sec", "name": None, "vars": []}]  # base file scope
    preamble: list[str] = []
    decl_ctx: dict[int, dict] = {}
    ext_imports: list[str] = []
    pending: list[str] = []      # prefix lines waiting for their declaration
    i, n = 0, len(lines)
    while i < n:
        line = lines[i]
        stripped = line.strip()
        # Skip comments wholesale, exactly as parse_module_items does. A docstring
        # line that happens to begin with `open`, `namespace`, `variable` or `end`
        # ("open condition, and the upper image is ...", "open TODO. B&M's ...")
        # otherwise lands in the preamble of every formal_statement built from
        # this file, as a line Lean cannot parse.
        if stripped.startswith(("/-", "/--")):
            depth = 0
            while i < n:
                depth += lines[i].count("/-") - lines[i].count("-/")
                i += 1
                if depth <= 0:
                    break
            continue
        if stripped.startswith("--") or not stripped:
            i += 1
            continue
        m_imp = IMPORT_LINE_RE.match(line)
        if m_imp:
            if not m_imp.group(1).startswith("TCSlib"):
                ext_imports.append(line.strip())
            i += 1
            continue
        if PREFIX_LINE_RE.match(line):
            pending.append(line.rstrip())
            i += 1
            continue
        if NS_RE.match(line):
            scopes.append({"kind": "ns", "name": NS_RE.match(line).group(1), "vars": []})
            pending = []
            i += 1
            continue
        if SECTION_RE.match(line):
            scopes.append({"kind": "sec", "name": None, "vars": []})
            pending = []
            i += 1
            continue
        if END_RE.match(line):
            if len(scopes) > 1:
                scopes.pop()
            pending = []
            i += 1
            continue
        if VAR_RE.match(line):
            j = variable_span_end(lines, i)
            scopes[-1]["vars"].append("\n".join(l.rstrip() for l in lines[i:j]))
            pending = []
            i = j
            continue
        if PREAMBLE_RE.match(line):
            ns = ".".join(s["name"] for s in scopes if s["kind"] == "ns" and s["name"])
            preamble.append((ns, line.rstrip()))
            pending = []
            i += 1
            continue
        if DECL_COL0_RE.match(line):
            ns = ".".join(s["name"] for s in scopes if s["kind"] == "ns" and s["name"])
            vrs = [v for s in scopes for v in s["vars"]]
            decl_ctx[i] = {"namespace": ns, "variables": vrs, "prefix": pending}
            pending = []
        elif not line[:1].isspace():
            pending = []      # any other column-0 command breaks a dangling prefix
        i += 1
    return preamble, decl_ctx, ext_imports


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
    depth = 0          # block-comment nesting from the scan start (a docstring opens one)
    for i in range(lo, len(lines)):
        line = lines[i]
        # A docstring line can begin with a keyword ("instance, assembled from ...")
        # and KIND_RE would take it for the declaration; only match outside comments.
        if depth == 0 and not line.lstrip().startswith(("--", "/-")):
            m = KIND_RE.match(line)
            if m:
                return i, m.group(1)
        depth = max(0, depth + line.count("/-") - line.count("-/"))
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
    """Keep the declaration type, including term-local let/have assignments.

    A top-level ``:=`` can bind a local name inside the result type rather than
    begin the proof. Ignore those assignments, as well as binder defaults,
    comments, strings and quoted identifiers, when locating the proof separator.
    """
    depth = 0
    pending_bindings = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i)
            i = n if end < 0 else end + 1
            continue
        if text.startswith("/-", i):
            comment_depth = 1
            i += 2
            while i < n and comment_depth:
                if text.startswith("/-", i):
                    comment_depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    comment_depth -= 1
                    i += 2
                else:
                    i += 1
            continue
        c = text[i]
        char_literal = c == "'" and i + 2 < n and (
            text[i + 2] == "'" or text[i + 1] == "\\"
        )
        if c == '"' or c == "«" or char_literal:
            closing = "»" if c == "«" else c
            i += 1
            while i < n:
                if closing in {'"', "'"} and text[i] == "\\":
                    i += 2
                elif text[i] == closing:
                    i += 1
                    break
                else:
                    i += 1
            continue
        if c in _OPEN_DELIM:
            depth += 1
        elif c in _CLOSE_DELIM:
            depth -= 1
        elif c.isalpha() or c == "_":
            end = i + 1
            while end < n and (text[end].isalnum() or text[end] in "_'"):
                end += 1
            if depth == 0 and text[i:end] in {"let", "letI", "have"}:
                pending_bindings += 1
            i = end
            continue
        elif depth == 0 and c == ":" and i + 1 < n and text[i + 1] == "=":
            if pending_bindings:
                pending_bindings -= 1
                i += 2
                continue
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
                file_cache[module] = (None, [], {}, [])
            else:
                lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
                preamble, decl_ctx, ext_imports = parse_file_context(lines)
                file_cache[module] = (lines, preamble, decl_ctx, ext_imports)
        return file_cache[module]

    # First pass: locate, classify, slice.
    for module, mdata in graph.items():
        lines, preamble, decl_ctx, ext_imports = load(module)
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
                ctx = decl_ctx[max(keys)] if keys else {"namespace": "", "variables": [], "prefix": []}
            slice_lines = lines[kidx:decl_end(lines, kidx)]
            raw[nname] = {
                "name": nname,
                "module": module,
                "kind": kind,
                "kidx": kidx,
                "namespace": ctx["namespace"],
                "variables": ctx["variables"],
                # Only the declaration the prefix was written for carries it: a nearest-
                # preceding fallback context must not re-attach `open Foo in`.
                "prefix": list(ctx.get("prefix", [])) if kidx in decl_ctx else [],
                "preamble": preamble,
                "ext_imports": ext_imports,
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
    full = "\n".join(rec["slice"])
    sig = split_signature(full)
    if sig == full.rstrip():
        # No top-level `:=` -- a `where`-style structure instance or definition. The
        # signature ends at the `where` keyword.
        m = re.search(r"\s+where\b", full)
        if m:
            sig = full[: m.start()].rstrip()
    return sig


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


def toposort(names: set[str], index, mod_rank: dict[str, int] | None = None) -> list[str]:
    """Dependencies before dependents; ties broken by (module, start) for determinism.

    With `mod_rank` (import-DAG postorder) ties follow the original import order, so a
    definition is never emitted before an instance from a module it imports, and every
    emitted dependency (lemma stubs included, via `all_deps`) counts, not only def-deps.
    """
    if mod_rank is not None:
        order_key = {n: (mod_rank.get(index[n]["module"], 10**9), index[n]["module"],
                         index[n]["kidx"]) for n in names}
        deps_of = lambda n: set(index[n]["def_deps"]) | (set(index[n].get("all_deps", [])) & names)  # noqa: E731
    else:
        order_key = {n: (index[n]["module"], index[n]["slice"][0] if index[n]["slice"] else "") for n in names}
        deps_of = lambda n: index[n]["def_deps"]  # noqa: E731
    remaining = set(names)
    emitted: list[str] = []
    placed: set[str] = set()
    while remaining:
        ready = sorted(
            (n for n in remaining if all(d in placed or d not in names for d in deps_of(n))),
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
    inner = list(rec["variables"]) + list(rec.get("prefix", []))
    if body:
        inner += rec["slice"]
    else:
        inner += [statement_text(rec) + " := sorry"]
    block = "\n".join(inner)
    ns = rec["namespace"]
    if ns:
        return f"namespace {ns}\n{block}\nend {ns}"
    return block


def make_formal_env(graph: dict, index) -> dict:
    """Per-run tables build_formal needs to reproduce a declaration's real environment.

    * `import_closure(m)`: the transitive TCSlib import closure of module m;
    * `ext_imports[m]`: m's non-TCSlib imports (what the module really elaborated under);
    * `mod_rank`: import-DAG postorder, for emission order;
    * `global_ns`: every namespace path any module enters (for `open` stubs);
    * `instances_by_module` / `refs`: candidate instances for the ambient widening and,
      lazily, the TCSlib declarations each one's text references.
    """
    mod_imports = build_module_imports(graph)
    mod_rank = build_module_ranks(mod_imports)
    short_map = build_any_short_map(index)
    global_ns: set[str] = set()
    instances_by_module: dict[str, list[str]] = {}
    ext_imports: dict[str, list[str]] = {}
    for nm, rec in index.items():
        ns = rec["namespace"]
        while ns:
            global_ns.add(ns)
            ns = ns.rpartition(".")[0]
        if rec["kind"] == "instance":
            instances_by_module.setdefault(rec["module"], []).append(nm)
        ext_imports.setdefault(rec["module"], rec.get("ext_imports", []))
    memo: dict[str, set[str]] = {}

    def import_closure(m: str) -> set[str]:
        if m not in memo:
            seen: set[str] = set()
            stack = [m]
            while stack:
                x = stack.pop()
                if x in seen:
                    continue
                seen.add(x)
                stack.extend(mod_imports.get(x, []))
            memo[m] = seen
        return memo[m]

    refs: dict[tuple[str, bool], set[str]] = {}

    def _text_refs(nm: str, strict: bool) -> set[str]:
        """TCSlib declarations the text of `nm` resolves to (same rules as ctx_refs_ok).

        `strict` leaves out the short-name fallback for dot-free tokens: it is the right
        guard for *dropping* a context command, but too eager a reason for *adding* a
        lemma stub (a bare `card` must not conjure up some `Foo.card`).
        """
        key = (nm, strict)
        if key not in refs:
            rec = index[nm]
            ns = rec["namespace"]
            found: set[str] = set()
            for tok in set(IDENT_RE.findall("\n".join(rec["slice"]))):
                cand = None
                if tok in index:
                    cand = tok
                elif ns and f"{ns}.{tok}" in index:
                    cand = f"{ns}.{tok}"
                elif "." in tok:
                    parent = tok.rsplit(".", 1)[0]
                    if parent in index:
                        cand = parent
                    elif ns and f"{ns}.{parent}" in index:
                        cand = f"{ns}.{parent}"
                elif not strict and tok in short_map:
                    cand = short_map[tok]
                if cand is not None and cand != nm:
                    found.add(cand)
            refs[key] = found
        return refs[key]

    sig_refs_memo: dict[str, set[str]] = {}

    def sig_refs(nm: str) -> set[str]:
        """TCSlib declarations an instance's signature (not its body) resolves to."""
        if nm not in sig_refs_memo:
            rec = index[nm]
            ns = rec["namespace"]
            found: set[str] = set()
            text = statement_text(rec) + "\n" + "\n".join(rec["variables"])
            for tok in set(IDENT_RE.findall(text)):
                cand = None
                if tok in index:
                    cand = tok
                elif ns and f"{ns}.{tok}" in index:
                    cand = f"{ns}.{tok}"
                elif "." in tok:
                    parent = tok.rsplit(".", 1)[0]
                    if parent in index:
                        cand = parent
                    elif ns and f"{ns}.{parent}" in index:
                        cand = f"{ns}.{parent}"
                if cand is not None and cand != nm:
                    found.add(cand)
            sig_refs_memo[nm] = found
        return sig_refs_memo[nm]

    return {"mod_imports": mod_imports, "mod_rank": mod_rank, "short_map": short_map,
            "global_ns": global_ns, "instances_by_module": instances_by_module,
            "ext_imports": ext_imports, "import_closure": import_closure,
            "text_refs": lambda nm: _text_refs(nm, False),
            "text_refs_strict": lambda nm: _text_refs(nm, True),
            "sig_refs": sig_refs}


def rewrite_open(line: str, ns: str, global_ns: set[str]) -> str:
    """`open Foo Bar` written inside `namespace A.B` -> the namespaces it resolved to.

    Lean resolves `open Foo` against the current namespace and its parents before the
    root (`A.B.Foo`, `A.Foo`, `Foo`).  The replayed command sits at top level, so the
    resolution is done here instead.  Modifier clauses (`(x y)`, `hiding`, `renaming`)
    are kept verbatim after the namespace tokens.
    """
    m = re.match(r"^(\s*open(?:\s+scoped)?\s+)(.*)$", line)
    if not m:
        return line
    head, rest = m.group(1), m.group(2)
    cut = len(rest)
    for marker in ("(", " hiding", " renaming"):
        pos = rest.find(marker)
        if pos >= 0:
            cut = min(cut, pos)
    names, tail = rest[:cut], rest[cut:]
    chain = []
    p = ns
    while p:
        chain.append(p)
        p = p.rpartition(".")[0]
    out = []
    for tok in names.split():
        resolved = tok
        for prefix in chain:
            if f"{prefix}.{tok}" in global_ns:
                resolved = f"{prefix}.{tok}"
                break
        out.append(resolved)
    sep = " " if tail and not tail[0].isspace() else ""
    return head + " ".join(out) + sep + tail


def lemma_stubs(names: set[str], index, env: dict) -> tuple[set[str], set[str]]:
    """Lemmas the bodies of `names` cite, and the definitions those lemmas' statements need.

    A definition's body may invoke a lemma (`⟨x, lemma_foo x⟩`, a `Fintype` instance
    built from a finiteness proof, a `Subtype` projection declared as a theorem).  The
    .ilean graph records the use, but the formal statement carries definitions only, so
    the body fails to elaborate standalone.  Such lemmas are emitted as `:= sorry` stubs:
    their statements (and the definitions those need), never their proofs.  Returns
    (stub lemmas, extra definitions), closed under the definitions' own lemma uses.
    """
    stubs: set[str] = set()
    extra: set[str] = set()
    todo = list(names)
    seen_defs = set(names)
    while todo:
        n = todo.pop()
        rec = index[n]
        for dep in (set(rec.get("all_deps", [])) | env["text_refs_strict"](n)):
            drec = index.get(dep)
            if drec is None or dep == n:
                continue
            if drec["kind"] in PROOF_KINDS and dep not in stubs:
                stubs.add(dep)
                for d in closure(drec["def_deps"], index):
                    if d not in seen_defs:
                        seen_defs.add(d)
                        extra.add(d)
                        todo.append(d)
    return stubs, extra


#: Classes whose instances are proofs: a `:= sorry` body is harmless (proof irrelevance),
#: whereas a sorried DATA instance (`MeasurableSpace`, `Fintype`, `MeasureSpace`) breaks
#: the definitional equalities later definitions rely on.  TCSlib classes declared `: Prop`
#: are recognised from their source; this list covers the Mathlib ones that occur.
PROP_CLASSES = {
    "IsProbabilityMeasure", "IsFiniteMeasure", "IsZeroOrProbabilityMeasure", "SigmaFinite",
    "IsLocallyFiniteMeasure", "NoAtoms", "IsMarkovKernel", "IsFiniteKernel",
    "DiscreteMeasurableSpace", "MeasurableSingletonClass", "BorelSpace", "OpensMeasurableSpace",
    "Nonempty", "Finite", "Infinite", "Countable", "Nontrivial", "NeZero", "Subsingleton",
    "IsEmpty", "Fact", "IsDomain", "NoZeroDivisors", "CharZero", "IsScalarTower",
    "SMulCommClass", "FaithfulSMul", "Std.Commutative", "Std.Associative", "IsSymmOp",
    "IsRefl", "IsTrans", "IsAntisymm", "IsTotal", "IsStrictOrder", "WellFoundedLT",
    "WellFoundedGT", "T2Space", "T1Space", "CompactSpace", "DiscreteTopology",
    "SecondCountableTopology", "FirstCountableTopology", "ContinuousMul", "ContinuousAdd",
    "ContinuousSMul", "OrderTopology", "LocallyCompactSpace", "ProperSpace", "CompleteSpace",
    "IsOpen", "IsClosed", "MeasurableSpace.CountablyGenerated", "StandardBorelSpace",
    "PolishSpace", "IsOrderedRing", "IsStrictOrderedRing", "IsOrderedAddMonoid",
    "IsOrderedMonoid", "NoMaxOrder", "NoMinOrder", "DenselyOrdered",
}


def instance_is_prop(rec, index) -> bool:
    """Does this instance inhabit a Prop-valued class (so its body is a proof)?"""
    sig = statement_text(rec)
    depth = 0
    last_colon = -1
    for i, c in enumerate(sig):
        if c in _OPEN_DELIM:
            depth += 1
        elif c in _CLOSE_DELIM:
            depth -= 1
        elif c == ":" and depth == 0 and sig[i:i + 2] != ":=":
            last_colon = i
    if last_colon < 0:
        return False
    head = IDENT_RE.search(sig[last_colon + 1:])
    if not head:
        return False
    name = head.group(0)
    if name in PROP_CLASSES or name.split(".")[-1] in PROP_CLASSES:
        return True
    ns = rec["namespace"]
    for cand in (name, f"{ns}.{name}" if ns else None):
        crec = index.get(cand) if cand else None
        if crec and crec["kind"] in ("class", "structure") and \
                re.search(r":\s*Prop\b", statement_text(crec)):
            return True
    return False


def ambient_instances(target, emitted: set[str], index, env: dict) -> tuple[set[str], set[str]]:
    """Instances of the target's environment that the emitted definitions make usable.

    Typeclass resolution leaves no trace in the .ilean dependency graph, so a statement
    about `HardSample n` compiles in its module (where `instance : MeasureSpace
    (HardSample n)` is in scope) and fails standalone.  Pull in every instance of the
    target's import closure -- or earlier in its own module -- whose TCSlib references
    are all already emitted or are lemmas (which become `:= sorry` stubs), to a fixpoint
    (an instance may build on another).
    """
    universe_mods = env["import_closure"](target["module"])
    cands = []
    for m in universe_mods:
        for nm in env["instances_by_module"].get(m, []):
            rec = index[nm]
            if m == target["module"] and rec["kidx"] >= target["kidx"]:
                continue
            if nm == target["name"] or "sorry" in "\n".join(rec["slice"]):
                continue
            cands.append(nm)
    cands.sort(key=lambda nm: (env["mod_rank"].get(index[nm]["module"], 10**9), index[nm]["kidx"]))
    have = set(emitted) | {target["name"]}
    added: set[str] = set()
    support: set[str] = set()
    changed = True
    while changed:
        changed = False
        for nm in cands:
            if nm in have:
                continue
            rec = index[nm]
            if instance_is_prop(rec, index):
                # A proof: emitted `:= sorry`, so only the signature must resolve.
                ok = env["sig_refs"](nm) <= have
            else:
                # Data: emitted with its real body, so everything the body cites must
                # already be present -- lemmas it cites become stubs (lemma_stubs).
                # (Pulling in the definitions a body needs instead was tried and lost:
                # such bodies then need instances of THEIR own that are not in scope.)
                refs = (set(rec["all_deps"]) | env["text_refs"](nm)) - have
                ok = set(rec["def_deps"]) <= have and all(
                    d in index and index[d]["kind"] in PROOF_KINDS for d in refs)
            if ok:
                have.add(nm)
                added.add(nm)
                changed = True
    return added, support


def build_formal(target, index, all_def_deps: bool, target_body: bool = False, env: dict | None = None):
    """The self-contained formal statement of `target` and its ordered definition closure.

    With `env` (from make_formal_env) the snippet reproduces the declaration's real
    environment: the external imports of its module's import closure instead of a
    blanket `import Mathlib`, the instances those definitions need, `universe` and
    `open`/`notation` context, the `open Foo in`-style prefixes written in front of each
    declaration, and namespace stubs so an `open` of a TCSlib namespace is legal before
    the namespace's first declaration.  Without `env` it is the legacy best-effort
    `import Mathlib` snippet.

    `target_body=True` emits the target with its body instead of `:= sorry` -- the
    form a *definition* needs when it is the thing being described (its body is its
    content), used by scripts/build_informal_statements.py --definitions.
    """
    seeds = seed_defs(target, index, all_def_deps)
    deps = closure(seeds, index)
    stubs: set[str] = set()          # lemmas emitted `:= sorry` (definition bodies cite them)
    ambient: set[str] = set()        # instances pulled in for typeclass resolution
    sorried: set[str] = set()        # Prop-valued ambient instances, emitted `:= sorry`
    if env is not None:
        # Definitions, the lemma stubs their bodies cite, and the ambient instances that
        # make them usable -- iterated, since a stub's statement can need a definition.
        while True:
            before = len(deps) + len(stubs) + len(ambient)
            new_stubs, extra = lemma_stubs((deps | ambient) - sorried, index, env)
            stubs |= new_stubs
            deps |= extra
            new_ambient, support = ambient_instances(target, deps | stubs | ambient, index, env)
            ambient |= new_ambient
            deps |= support
            sorried |= {n for n in new_ambient if instance_is_prop(index[n], index)}
            if len(deps) + len(stubs) + len(ambient) == before:
                break
        stubs.discard(target["name"])
    ordered = toposort(deps | stubs | ambient, index, env["mod_rank"] if env else None)
    emitted = set(ordered) | {target["name"]}

    # Preamble: union of open/notation/set_option/universe lines from all contributing
    # modules (each module once, in import order).  A notation that names a TCSlib
    # declaration outside the closure cannot elaborate and is dropped.  A command
    # written inside `namespace A` is replayed in that namespace: `scoped`/notation
    # lines are wrapped in `namespace A ... end A`, and an `open Foo` is rewritten to
    # the namespace it resolved to there (`A.Foo` when that exists), since at top level
    # `open Foo` would name a namespace that does not exist.
    preamble: list[str] = []
    seen_pre = set()
    mods_seen: set[str] = set()
    for n in ordered + [target["name"]]:
        rec = index[n] if n in index else target
        if rec["module"] in mods_seen:
            continue
        mods_seen.add(rec["module"])
        for entry in rec["preamble"]:
            ns, line = entry if isinstance(entry, tuple) else ("", entry)
            if env is not None and NOTATION_LINE_RE.match(line) and \
                    not ctx_refs_ok(line, ns, index, env["short_map"], emitted):
                continue
            stripped = line.strip()
            if ns and env is not None and stripped.startswith("open"):
                line = rewrite_open(line, ns, env["global_ns"])
            elif ns and (stripped.startswith("scoped") or
                         (NOTATION_LINE_RE.match(line) and not stripped.startswith("local"))):
                line = f"namespace {ns}\n{line}\nend {ns}"
            if line in seen_pre:
                continue
            seen_pre.add(line)
            preamble.append(line)

    if env is not None:
        universe_mods = env["import_closure"](target["module"])
        imports: list[str] = []
        seen_imp = set()
        for m in sorted(universe_mods, key=lambda m: (env["mod_rank"].get(m, 10**9), m)):
            for line in env["ext_imports"].get(m, []):
                if line not in seen_imp:
                    seen_imp.add(line)
                    imports.append(line)
        if not imports:
            imports = ["import Mathlib"]
    else:
        imports = ["import Mathlib"]

    body_parts: list[str] = []
    if preamble:
        body_parts += preamble + [""]
    for n in ordered:
        body_parts.append(emit_block(
            index[n], body=index[n]["kind"] not in PROOF_KINDS and n not in sorried))
        body_parts.append("")
    body_parts.append(emit_block(target, body=target_body))
    body = "\n".join(body_parts)

    ns_stubs: list[str] = []
    if env is not None:
        seen_stub: set[str] = set()
        for mline in re.finditer(r"^\s*open\s+(.+)$", body, re.MULTILINE):
            for tok in mline.group(1).replace(" in", " ").split():
                tok = tok.strip("()")
                if tok in ("scoped", "in") or not tok:
                    continue
                for ns in sorted(env["global_ns"]):
                    if (ns == tok or ns.endswith("." + tok)) and ns not in seen_stub:
                        seen_stub.add(ns)
                        ns_stubs.append(f"namespace {ns}\nend {ns}")

    parts = imports + [""] + (ns_stubs + [""] if ns_stubs else []) + [body]
    upstream = [n for n in ordered if index[n]["kind"] not in PROOF_KINDS]
    return "\n".join(parts).rstrip() + "\n", upstream


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
        # Each module's items sit in their own `section`: `set_option`, `universe` and
        # `open` commands are section-scoped, so a module's options (e.g. `autoImplicit
        # false`) and universe names no longer leak into the next module's items, and a
        # module's `universe u` is not re-declared at top level by the module after it.
        # This is what "for the rest of the original module" meant in the first place.
        parts.append("section")
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
        parts.append("end")
        parts.append("")

    # Namespace stubs: `open Foo` errors when namespace Foo is not registered yet, and
    # an emitted open may fire before (or without) any declaration in that namespace.
    # Scan the assembled body's open lines and pre-register every TCSlib namespace they
    # mention. An `open Foo` that render_item hoisted out of `namespace NS` resolves
    # relative to NS, so `NS.Foo` (any registered namespace ending in `.Foo`) is stubbed
    # as well. (Registering a namespace that later collides with a declaration name is
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
            for ns in sorted(global_ns):
                if ns == tok or ns.endswith("." + tok):
                    if ns not in seen_stub:
                        seen_stub.add(ns)
                        stubs.append(f"namespace {ns}\nend {ns}")

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

    # The .ilean-derived graph also misses references inside `match` arms, `let rec` /
    # `where` helpers and other nested scopes of INDEXED declarations (a flattened file
    # then fails with "unknown constant"). Widen every declaration's deps with a
    # conservative token scan: exact names, names relative to the declaration's own
    # namespace (or an enclosing one), the parent of a dotted projection, and — for
    # dot-free tokens only — an unambiguous short name. Only declarations in the
    # module's import closure qualify, so a scan can add a real dependency but never
    # one the original module could not see.
    for nm, rec in pindex.items():
        visible = import_closure(rec["module"])
        ns = rec.get("namespace") or ""
        prefixes = []
        while ns:
            prefixes.append(ns)
            ns = ns.rpartition(".")[0]
        deps = set(rec["all_deps"])
        for tok in set(IDENT_RE.findall("\n".join(rec["slice"]))):
            cand = None
            if tok in pindex:
                cand = tok
            else:
                for p in prefixes:
                    if f"{p}.{tok}" in pindex:
                        cand = f"{p}.{tok}"
                        break
                if cand is None and "." in tok:
                    parent = tok.rsplit(".", 1)[0]
                    if parent in pindex:
                        cand = parent
                    else:
                        for p in prefixes:
                            if f"{p}.{parent}" in pindex:
                                cand = f"{p}.{parent}"
                                break
                elif cand is None and tok in short_map:
                    cand = short_map[tok]
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
    ap.add_argument("--only", nargs="+", default=None, metavar="NAME",
                    help="Only emit these theorems (fully-qualified Lean names). Used to "
                         "regenerate a handful of records and splice them into an "
                         "existing dataset with scripts/dataset_splice.py.")
    ap.add_argument("--modules", nargs="+", default=None, metavar="MODULE",
                    help="Only emit theorems of these modules: `TCSlib.A.B`, the suffix "
                         "`A.B`, or an area such as `Complexity` (every module under it).")
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
    formal_env = make_formal_env(graph, index)

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
    # The informal half's two sources: a cited passage of a reference text when the
    # entry cites one, else the Lean-derived prose composed below (plus the
    # informalized proof account when a note exists).  No model call: everything is
    # read from the blueprint, references/<doc>.md and references/informalized/.
    isrc = _informal_sources()
    citations = isrc.blueprint_citations()
    block_text = isrc.load_block_text()
    notes = isrc.load_notes()
    print(f"  {sum(1 for n in citations if isrc.is_cited(n, citations))} cited entries, "
          f"{len(block_text)} reference documents, {len(notes)} informalized notes.")
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

    # Difficulty is the blueprint's intrinsic, tactic-only \difficulty rating (0–7):
    # how nonobvious this declaration's own tactic script is, rated in isolation from
    # its dependencies. No upstream aggregation over the proof dep graph.
    def intrinsic(name):
        e = lookup(name)
        return e.get("difficulty") if e else None

    def compose(entry, name=None):
        r"""Fold the [title] into the prose so the text reads as a statement.

        A blueprint title is often just the declaration's own Lean name -- either
        verbatim (``finrank\_inf\_pos\_iff\_dvd\_tau``) or merely re-spaced
        (``two_mul_xDistance_sq_le_xFiberKL`` -> "Two Mul Xdistance Sq Le
        Xfiberkl").  Folding that in would open the *informal* statement with the
        *formal* identifier it is supposed to be paired against, so such a title
        is dropped and only the prose is kept.  It is still reported by
        ``scripts/dataset_hygiene.py`` so the blueprint can be given a real title.
        """
        t = (entry.get("title") or "").strip()
        b = (entry.get("informal") or "").strip()
        if t and name and is_name_title(t, name):
            t = ""
        if t and b and _squash_prose(b).startswith(_squash_prose(t)):
            # The prose already opens with the title (both are derived from the
            # same docstring summary line); do not say it twice.
            t = ""
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
    if args.only:
        wanted = set(args.only)
        missing = sorted(wanted - set(targets))
        if missing:
            print(f"ERROR: --only names not indexed as theorems/lemmas: {missing}")
            return 1
        targets = [n for n in targets if n in wanted]
    if args.modules:
        targets = [n for n in targets if module_matches(index[n]["module"], args.modules)]
        if not targets:
            print(f"ERROR: --modules {args.modules} selects no theorem in dep_graph.json")
            return 1
    if args.limit:
        targets = targets[: args.limit]

    out_path = Path(args.out).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)

    n_written = n_missing = 0
    total_defs = 0
    n_by_source = {"citation": 0, "lean": 0}
    unresolved_citations: list[tuple[str, str, str]] = []
    proof_lines_total = proof_lines_max = n_proof_unresolved = 0
    with open(out_path, "w", encoding="utf-8") as f:
        for name in targets:
            rec = index[name]
            info = lookup(name)
            if info is None:
                n_missing += 1
                continue
            formal, ordered = build_formal(rec, index, args.all_def_deps, env=formal_env)
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
            stmt = compose(info, name)
            if definitions:
                defs_block = "\n".join(f"- {compose(d, d['id'])}" for d in definitions)
                lean_prose = f"Definitions:\n{defs_block}\n\nStatement: {stmt}"
            else:
                lean_prose = stmt
            informal_statement, informal_source, unresolved = isrc.informal_column(
                name, lean_prose, citations, block_text, notes)
            n_by_source[informal_source] += 1
            for document, block in unresolved:
                unresolved_citations.append((name, document, block))

            record = {
                "id": name,
                "informal_statement": informal_statement,
                "informal_source": informal_source,
                "formal_statement": formal,
                "lean_name": name,
                "title": info["title"],
                "definitions": definitions,
                "source_module": rec["module"],
                "kind": rec["kind"],
                "upstream_defs": ordered,
                "n_upstream_defs": len(ordered),
                # Intrinsic 0–7 rating of this proof's own tactic script; null only
                # when unrated (bare-sorry proofs are never rated, so they stay null).
                # An upstream sorry does NOT null the rating — it rates this proof's
                # own tactics, and `proof_complete` already flags incomplete closures.
                "difficulty": intrinsic(name),
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

    # The theorems web viewer (webpage/theorems/index.html) fetches the gzipped
    # copy in preference to the .jsonl, so the .gz must be refreshed in the same
    # run or the viewer silently serves a stale dataset. Written via a temp file
    # so an interrupted run can't leave a truncated .gz behind.
    gz_path = out_path.with_suffix(out_path.suffix + ".gz")
    gz_tmp = gz_path.with_suffix(gz_path.suffix + ".tmp")
    with open(out_path, "rb") as src, gzip.open(gz_tmp, "wb", compresslevel=9) as dst:
        shutil.copyfileobj(src, dst)
    gz_tmp.replace(gz_path)

    print()
    print(f"Wrote {n_written} records -> {display_output_path(out_path)}")
    print(f"Refreshed gzip copy -> {display_output_path(gz_path)}")
    print(f"Theorems without a blueprint informal statement (skipped): {n_missing}")
    if n_written:
        print(f"Avg upstream definitions per theorem: {total_defs / n_written:.1f}")
        print(f"informal_source: {n_by_source['citation']} citation, {n_by_source['lean']} lean")
    if n_written and proof_builder is not None:
        print(f"Proof files: avg {proof_lines_total / n_written:.0f} lines, "
              f"max {proof_lines_max} lines; "
              f"{n_proof_unresolved} records with unresolved deps")
    if unresolved_citations:
        print(f"Citations whose blocks are missing from the reference .md "
              f"(the record fell back to `lean`): {len(unresolved_citations)}")
        for name, document, block in unresolved_citations[:10]:
            print(f"  {name} -> {document}: {block}")
        if len(unresolved_citations) > 10:
            print(f"  ... and {len(unresolved_citations) - 10} more")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
