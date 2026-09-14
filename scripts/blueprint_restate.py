r"""Rebuild the *statement* prose of the blueprint.

Why
---
`blueprint/src/chapter/GraphTheory/Core/*.tex` was machine-generated from the
Lean docstrings by a `blueprint_from_docstring.py` that no longer exists.  That
generator kept the wrong half of each docstring: it emitted the **Reading** and
**Formalisation** commentary and dropped the statement, so the dataset built on
top of it (`dataset/tcslib_theorems.jsonl`) carried proof sketches, proof plans
("Step 3 is the mathematical core"), repo status notes ("Currently vacuous ---
`IsSpanningTree` has a `sorry` body") and Lean-internal formalisation asides in
the `informal_statement` field -- and in 452 of 528 entries carried no statement
of the theorem at all.

The blueprint contract (`.claude/agents/blueprint-writer.md`) is explicit:
*"state the claim (hypotheses => conclusion).  Describe the statement, never the
proof."*  This script restores that contract for the twelve GraphTheory chapters
by re-deriving each environment body from the statement sections of its Lean
docstring.

What counts as a statement section
----------------------------------
The docstrings are sectioned by bold or ``##`` headers.  Kept:

  * the opening prose (a one-line summary of what the declaration says);
  * ``**Book definition**`` / ``**Book statement**`` / ``**Theorem 8.4**`` /
    ``**Exercise 8.1.8**`` / ``**Corollary 10.1**`` / ... -- the verbatim claim.

Dropped:

  * ``**Book proof**``, ``**Proof**``, ``**Proof plan**``, ``**Skeleton**`` --
    the proof;
  * ``**Reading**`` -- significance commentary, which routinely gives the proof
    idea away;
  * ``**Formalisation**`` -- Lean/Mathlib implementation notes;
  * ``**In Lean notation**``, ``**Note on ...**``, ``**Book usage/context**``;
  * any sentence flagged with the ``WARNING`` glyph -- repo status notes.

Regenerated statements
----------------------
A second stage then runs over *every* chapter, not just GraphTheory.  Wherever
`scripts/build_informal_statements.py` has cached a regenerated statement for a
declaration, that statement replaces the entry's body and its `[title]`.  Those
are written from the formal statement to handout standard -- every object
introduced, every hypothesis rendered, mathematics in mathematical notation --
which the blueprint's own prose frequently was not.

The two stages compose: stage one gives a GraphTheory entry its book statement,
stage two overwrites it when a regenerated statement exists (theorems and
lemmas), so definitions keep the book's wording and claims get the rewritten
prose.  Metadata (`\lean`, `\uses`, `\difficulty`, `\proofsource`, ...) is
carried through untouched by both.

Usage
-----
    python3 scripts/blueprint_restate.py --check     # report, touch nothing
    python3 scripts/blueprint_restate.py             # both stages
    python3 scripts/blueprint_restate.py --no-apply  # docstring stage only
    python3 scripts/blueprint_restate.py --apply-only # regenerated stage only
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import md_to_tex as M  # noqa: E402

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))
TEX_DIR = BASE / "blueprint" / "src" / "chapter" / "GraphTheory" / "Core"
LEAN_DIR = BASE / "TCSlib" / "GraphTheory" / "Core"
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"

from proofmatch import statements as cache  # noqa: E402

# `scripts/proofmatch.py` shadows the package on sys.path, so the sibling module
# is loaded by path.
import importlib.util  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "statement_quality", Path(__file__).resolve().parent / "statement_quality.py"
)
Q = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(Q)

BEGIN_RE = re.compile(r"\\begin\{(theorem|lemma|definition|proposition|corollary|sublemma)\}")
END_RE = re.compile(r"\\end\{(theorem|lemma|definition|proposition|corollary|sublemma)\}")
LEAN_BIND_RE = re.compile(r"^\s*\\lean\{([^}]*)\}\s*$")
#: Metadata lines that must survive verbatim; everything else in a body is prose.
META_RE = re.compile(
    r"^\s*\\(lean|label|leanok|uses|difficulty|proofsource|statementsource|proofstep)\b(.*)$"
)
#: How many brace groups each metadata macro takes.  `\proofstep` writes its four
#: arguments on the lines *after* the macro name, so counting braces on the macro
#: line alone stops the scan immediately and spills the arguments into the prose
#: -- where a body rewrite then deletes them.
META_ARITY = {
    "lean": 1, "label": 1, "leanok": 0, "uses": 1, "difficulty": 1,
    "proofsource": 2, "statementsource": 2, "proofstep": 4,
}


def consume_macro_args(text: str, pending: int, depth: int) -> tuple[int, int]:
    """Advance the (arguments-left, brace-depth) state across one more line."""
    for ch in text:
        if ch == "{":
            if depth == 0:
                pending -= 1
            depth += 1
        elif ch == "}" and depth > 0:
            depth -= 1
        if pending <= 0 and depth == 0:
            return 0, 0
    return max(pending, 0), depth

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+|scoped\s+|local\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque)\s+([^\s({\[:]+)"
)

WARN = "\u26a0"


# --------------------------------------------------------------------------- #
# Lean docstrings
# --------------------------------------------------------------------------- #
def docstrings(path: Path) -> dict[str, str]:
    """Declaration name -> the `/-- ... -/` docstring immediately above it."""
    text = path.read_text(encoding="utf-8")
    out: dict[str, str] = {}
    i = 0
    while True:
        s = text.find("/--", i)
        if s < 0:
            break
        e = text.find("-/", s)
        if e < 0:
            break
        doc = text[s + 3:e].strip()
        for line in text[e + 2:].split("\n"):
            if not line.strip() or line.lstrip().startswith(("--", "/-")):
                continue
            m = DECL_RE.match(line)
            if m:
                #: `inductive Network.IncPath.{u} ...` -- drop the universe annotation
                #: that would otherwise leave a trailing dot on the name.
                out[m.group(2).rstrip(".")] = doc
            break
        i = e + 2
    return out


def lookup(docs: dict[str, str], binding: str) -> str | None:
    """Match a blueprint `\\lean{A.B.c}` label to a docstring keyed by `B.c` or `c`."""
    if binding in docs:
        return docs[binding]
    parts = binding.split(".")
    for i in range(1, len(parts)):
        k = ".".join(parts[i:])
        if k in docs:
            return docs[k]
    cands = [k for k in docs if k.split(".")[-1] == parts[-1]]
    return docs[cands[0]] if len(cands) == 1 else None


# --------------------------------------------------------------------------- #
# Statement / commentary split
# --------------------------------------------------------------------------- #
KEEP_HDR = re.compile(
    r"^(book\s+(statement|definition|assertion|observation|equation|quantity|notation|"
    r"convention|construction|remark|formula|terminology|theorem|corollary|lemma|exercise)\b"
    r"|the\s+book(’|')?s?\s+own\s+statement"
    r"|statement\b"
    r"|(theorem|corollary|lemma|proposition|definition|exercise|thm|cor|lem|prop|ex)\b\s*[0-9(]"
    r")",
    re.I,
)
DROP_HDR = re.compile(
    r"^(book\s+proof|proof|skeleton|reading|formalis|formaliz|step\b|book\s+usage|"
    r"book\s+context|in\s+lean\s+notation|note\s+on|why\b|caveat|status|defect|warning|"
    r"provenance|restored\s+transcription|the\s+repair|repair\b|audit\b|triage\b|"
    + WARN + r")",
    re.I,
)

#: Whole paragraphs that are bookkeeping about the formalisation effort rather
#: than mathematics.  Matched against a paragraph's full text.
META_PARA = re.compile(
    r"(?ix)^\s*(?:"
    r"an?\s+(?:starred\s+)?exercise,\s+so\s+the\s+book\s+gives\s+no\s+proof"
    r"|(the\s+)?book\s+gives\s+no\s+proof"
    r"|no\s+proof\s+in\s+the\s+book"
    r"|the\s+book\s+states\s+this\s+without\s+proof"
    r")\b"
)

#: A formalisation aside: a sentence about how the Lean says it, not about what
#: the mathematics claims.  These never occur inside the book's own words, so the
#: filter that uses this only runs on non-quoted prose.
FORMALISATION_SENTENCE = re.compile(
    r"(?ix)("
    r"\bNat\.card\b|\bFintype\b|\bDecidableRel\b|\bDecidableEq\b|\bClassical\b"
    r"|\bSubgraph\.mk\b|\binstances?\s+discharge\b|\bwell-typed\b|\belaborat"
    r"|\b(?:in|on)\s+the\s+repo\b|\brepo\s+has\b|\brepo\s+`|\.lean\b|\bMathlib(?:'s)?\s+(?:own\s+)?"
    r"(?:idiom|has|supplies|proves|calls)\b|\bthin\s+shorthand\b|\bopaque\s+stub\b"
    r"|\bthe\s+outline\b|\bdo\s+\*\*?not\*\*?\s+use\b|\bNOTE\s*:"
    r")"
)

#: A paragraph opening with `NOTE:` is always a formalisation aside.
NOTE_PARA = re.compile(r"(?i)^\s*NOTE\s*[:.]")

#: Short self-contained asides about the *repo* that the docstrings append to
#: their summary line.  Each is a complete sentence or parenthetical, so
#: deleting it leaves the surrounding prose intact.
REPO_ASIDE = re.compile(
    r"(?x)"
    r"\(NEEDED-TO-STATE[^)]*\)\s*"
    r"|\(Repo\s+`[^`]*`\.?\)\s*"
    r"|\(Mathlib\s+has\s+no[^)]*\)\s*"
    r"|\([^)]*audit\s+judgement[^)]*\)\s*"
    r"|(?:Structural\s+predicate;\s*)?Body\s+deferred(?:\s*\([^)]*\)|[^.]*)?\.\s*"
    r"|NOT\s+a\s+missing\s+def\.\s*"
    r"|Honest\s+(?:def|replacement)[^.]*\.\s*"
    r"|MISSING\s+from\s+Mathlib[^.]*\.\s*"
    r"|\d+\s+hits?\s+in\s+Mathlib\.\s*"
    r"|Do\s+\*\*not\*\*\s+re-derive[^.]*\.\s*"
)
BOLD_HDR = re.compile(r"^\*\*(.+?)\*\*", re.S)
HASH_HDR = re.compile(r"^#{1,6}\s+(.+?)\s*$")


def paragraphs(doc: str) -> list[str]:
    return [p for p in re.split(r"\n[ \t]*\n", doc) if p.strip()]


def section_header(para: str) -> str | None:
    s = para.strip()
    m = HASH_HDR.match(s.split("\n", 1)[0])
    if m:
        return m.group(1)
    m = BOLD_HDR.match(s)
    if m and len(m.group(1)) <= 90:
        return m.group(1).strip()
    return None


def statement_paragraphs(doc: str) -> list[str]:
    """The paragraphs of `doc` that state the claim, in order."""
    kept: list[str] = []
    keeping = True
    for para in paragraphs(doc):
        h = section_header(para)
        if h is not None:
            hh = h.strip().lstrip("*").strip()
            if DROP_HDR.match(hh):
                keeping = False
            elif KEEP_HDR.match(hh):
                keeping = True
        if keeping:
            kept.append(para)
    return kept


#: `**Theorem 8.4** (Brooks, 1941).` / `## Book statement (§5.3, p. 84) — verbatim`
#: -- the label and its provenance are bookkeeping, not mathematics.
LABEL_RE = re.compile(r"^\*{1,2}(.+?)\*{1,2}\s*", re.S)
PROVENANCE_RE = re.compile(
    r"^\((?:B&M\s*)?[^()]*(?:§|verbatim|p\.\s*\d|pp\.\s*\d)[^()]*\)\s*[.,]?\s*", re.I
)
TRAILING_PROVENANCE_RE = re.compile(r"\s*[—-]{1,3}\s*verbatim[^\n]*$", re.I)


def strip_label(para: str) -> str:
    """Remove a leading section label and any `(B&M §5.3, verbatim)` provenance."""
    if re.match(r"^\s{4,}\S", para):      # an indented code block carries no label
        return para.rstrip()
    #: A verbatim book quote arrives as a `>` blockquote; unwrap it first so the
    #: `**Theorem 5.4**` inside is recognised as the label it is.
    para = re.sub(r"^[ \t]*>[ \t]?", "", para, flags=re.M)
    s = para.strip()
    m = HASH_HDR.match(s.split("\n", 1)[0])
    if m:
        s = s.split("\n", 1)[1] if "\n" in s else ""
        return s.strip()
    m = LABEL_RE.match(s)
    if m and KEEP_HDR.match(m.group(1).strip()):
        # `**Theorem 8.4** (Brooks, 1941).` -- the label is bookkeeping, the
        # attribution is not.  A bold that is not a section label (`**Feasibility**
        # for supplies ...`) is the term being defined and must stay.
        s = s[m.end():]
        s = PROVENANCE_RE.sub("", s)
        #: `**Exercise 3.1.3(a)**: a simple graph ...` -- the punctuation that
        #: attached the label to the sentence goes with the label.
        s = re.sub(r"^[.,:;]\s*", "", s)
        s = s[:1].upper() + s[1:] if s[:1].islower() else s
    return s.strip()


SENT_SPLIT_RE = re.compile(r"(?<=[.!?])\s+(?=[A-Z(`*\\$])")


def is_quoted(para: str) -> bool:
    """True for a verbatim book quote: a `>` blockquote or a whole-paragraph `*...*`."""
    s = para.strip()
    return s.startswith(">") or (s.startswith("*") and s.endswith("*") and "**" not in s[:2])


def drop_formalisation_sentences(para: str) -> str:
    """Drop formalisation asides from non-quoted prose, keeping the mathematics."""
    if is_quoted(para):
        return para
    sentences = SENT_SPLIT_RE.split(para.replace("\n", " "))
    if len(sentences) < 2:
        return para
    keep = [s for s in sentences if not FORMALISATION_SENTENCE.search(s)]
    if not keep:
        return para           # nothing but asides: leave it rather than empty the entry
    return " ".join(keep)


def drop_warnings(para: str) -> str:
    """Delete repo status notes -- the WARNING glyph and the sentence carrying it."""
    if WARN not in para:
        return para
    out = []
    for line in para.split("\n"):
        if WARN in line:
            head = line.split(WARN, 1)[0].rstrip()
            # A warning mid-paragraph swallows the rest of the paragraph: these
            # notes run to the end of their block in every docstring in the tree.
            if head:
                out.append(head)
            break
        out.append(line)
    return "\n".join(out).strip()


# --------------------------------------------------------------------------- #
# Markdown -> LaTeX
# --------------------------------------------------------------------------- #
CODE_SPAN_RE = re.compile(r"`([^`]+)`")
BOLD_RE = re.compile(r"\*\*([^*]+)\*\*")
EMPH_RE = re.compile(r"(?<!\*)\*([^*\n][^*]*?)\*(?!\*)")
DISPLAY_RE = re.compile(r"\$\$(.+?)\$\$", re.S)


#: Markdown backslash escapes (`4.2.4\*`, `foo\_bar`) -- the backslash is markup.
MD_ESCAPE_RE = re.compile(r"\\([*_#`\[\]])")

#: HTML entities the docstrings use for indentation inside blockquotes.
HTML_ENTITY_RE = re.compile(r"&nbsp;|&thinsp;|&emsp;|&ensp;")


def convert_inline(text: str) -> str:
    """One paragraph of markdown prose -> LaTeX, code spans and math preserved."""
    holes: list[str] = []

    def stash(s: str) -> str:
        holes.append(s)
        return f"\x00{len(holes) - 1}\x00"

    text = DISPLAY_RE.sub(lambda m: stash("\\[" + M.math(m.group(1).strip()) + "\\]"), text)
    text = re.sub(r"\$([^$]+)\$", lambda m: stash("$" + M.math(m.group(1)) + "$"), text)
    text = CODE_SPAN_RE.sub(lambda m: stash(M.texttt(m.group(1))), text)
    text = MD_ESCAPE_RE.sub(r"\1", text)
    text = BOLD_RE.sub(lambda m: stash(r"\textbf{" + M.prose(m.group(1)) + "}"), text)
    text = EMPH_RE.sub(lambda m: stash(r"\emph{" + M.prose(m.group(1)) + "}"), text)
    text = M.prose(text)
    #: Stashed spans can themselves contain stashes (a code span inside `*...*`),
    #: so expand until the text is placeholder-free.
    hole_re = re.compile(r"\x00(\d+)\x00")
    while hole_re.search(text):
        text = hole_re.sub(lambda m: holes[int(m.group(1))], text)
    return text


def convert_paragraph(para: str) -> str:
    """A whole paragraph, including blockquote markers and indented code blocks."""
    lines = para.split("\n")
    if all(re.match(r"^\s{4,}\S", ln) or not ln.strip() for ln in lines):
        body = [r"\texttt{" + M.texttt(ln.strip())[len(r"\texttt{"):-1] + "}"
                for ln in lines if ln.strip()]
        return "\\begin{quote}\n" + "\\\\\n".join(body) + "\n\\end{quote}"
    lines = [re.sub(r"^\s*>\s?", "", ln) for ln in lines]
    return convert_inline(HTML_ENTITY_RE.sub(" ", "\n".join(lines)).strip())


def wrap(text: str, width: int = 88) -> str:
    """Re-flow to the width the rest of the blueprint uses, never inside a command."""
    out_lines = []
    for para in text.split("\n"):
        if para.startswith(("\\begin", "\\end", "\\[", "\\texttt")) or len(para) <= width:
            out_lines.append(para)
            continue
        cur = ""
        for word in para.split(" "):
            if cur and len(cur) + 1 + len(word) > width:
                out_lines.append(cur)
                cur = word
            else:
                cur = f"{cur} {word}".strip()
        if cur:
            out_lines.append(cur)
    return "\n".join(out_lines)


def render(doc: str) -> str:
    """The blueprint body for one declaration: its statement, and nothing else."""
    md: list[str] = []
    for para in statement_paragraphs(doc):
        para = drop_warnings(strip_label(drop_warnings(para)))
        if META_PARA.match(para) or NOTE_PARA.match(para):
            continue
        para = REPO_ASIDE.sub("", para).strip()
        para = drop_formalisation_sentences(para).strip()
        if not para.strip():
            continue
        md.append(para)
    #: A paragraph that is nothing but a formalisation aside goes, but only while
    #: something else is left to state the claim.
    aside = [i for i, q in enumerate(md)
             if not is_quoted(q) and len(SENT_SPLIT_RE.split(q.replace("\n", " "))) == 1
             and FORMALISATION_SENTENCE.search(q)]
    if len(aside) < len(md):
        md = [q for i, q in enumerate(md) if i not in set(aside)]
    paras = []
    for para in md:
        tex = convert_paragraph(para)
        if tex.strip():
            paras.append(wrap(tex))
    return "\n\n".join(paras).strip()


# --------------------------------------------------------------------------- #
# Rewriting
# --------------------------------------------------------------------------- #
def rewrite_file(tex: Path, docs: dict[str, str], report: list) -> str | None:
    lines = tex.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    i = 0
    changed = False
    while i < len(lines):
        mb = BEGIN_RE.search(lines[i])
        if not mb:
            out.append(lines[i])
            i += 1
            continue
        out.append(lines[i])
        begin_line = lines[i]
        i += 1
        meta: list[str] = []
        prose: list[str] = []             # the existing body, kept if we cannot rebuild it
        binding = None
        pending = depth = 0               # arguments still owed by a multi-line macro
        while i < len(lines) and not END_RE.search(lines[i]):
            line = lines[i]
            if pending > 0 or depth > 0:
                meta.append(line)
                pending, depth = consume_macro_args(line, pending, depth)
            elif (mm := META_RE.match(line)):
                meta.append(line)
                pending, depth = consume_macro_args(mm.group(2), META_ARITY[mm.group(1)], 0)
                m = LEAN_BIND_RE.match(line)
                if m:
                    first = m.group(1).split(",")[0].strip()
                    if first and not first.startswith("["):
                        binding = first
            else:
                prose.append(line)
            i += 1
        end_line = lines[i] if i < len(lines) else r"\end{theorem}"
        doc = lookup(docs, binding) if binding else None
        if doc is None:
            report.append((tex.name, binding, "no-docstring"))
            body = None
        else:
            body = render(doc)
            if not body:
                report.append((tex.name, binding, "empty-statement"))
                body = None
        out.extend(meta)
        if body is not None:
            out.append(body)
            changed = True
        else:
            # Nothing to rebuild from: keep whatever the entry already said rather
            # than silently emptying it.
            out.extend(prose)
            report.append((tex.name, binding, "left-as-is"))
        out.append(end_line)
        i += 1
    return "\n".join(out) + "\n" if changed else None




# --------------------------------------------------------------------------- #
# Stage 2: regenerated statements
# --------------------------------------------------------------------------- #
#: A blueprint title lives inside `\begin{env}[...]`, so a bare `]` would end it
#: early and an unbalanced brace would swallow the entry.
def safe_title(title: str) -> str | None:
    title = " ".join((title or "").split()).rstrip(".")
    if not title or title.count("{") != title.count("}"):
        return None
    if "[" in title or "]" in title:
        # `Case analysis on the $\mathrm{AC}^0[p]$ gate set` -- brace-guard it,
        # the convention `build_dataset.env_title` already peels back off.
        return "{" + title + "}"
    return title


def title_span(line: str, pos: int) -> tuple[int, int] | None:
    """(start, end) of the `[...]` title whose `\begin{env}` ends at `pos`."""
    if pos >= len(line) or line[pos] != "[":
        return None
    depth = 0
    i = pos + 1
    while i < len(line):
        c = line[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        elif c == "]" and depth <= 0:
            return pos + 1, i
        i += 1
    return None


def apply_cached(tex: Path, entries: dict[str, dict], report: list) -> str | None:
    """Replace each entry's body and title with its regenerated statement.

    The prose it displaces is stashed in the cache entry the first time, so the
    stage is idempotent *and* reversible: re-running after a statement stops
    passing the typesetting guard puts the blueprint's own words back, instead
    of leaving the last bad version sitting in the document.
    """
    lines = tex.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    i = 0
    changed = False
    while i < len(lines):
        mb = BEGIN_RE.search(lines[i])
        if not mb:
            out.append(lines[i])
            i += 1
            continue
        begin_idx = len(out)
        begin_line = lines[i]
        out.append(begin_line)
        span = title_span(begin_line, mb.end())
        i += 1
        meta: list[str] = []
        prose: list[str] = []
        #: An environment may bind several declarations to one body
        #: (`\lean{boolToSign_sq, boolToSign_not}`); any of them may carry the
        #: cached statement, so collect them all.
        bindings: list[str] = []
        pending = depth = 0               # arguments still owed by a multi-line macro
        while i < len(lines) and not END_RE.search(lines[i]):
            line = lines[i]
            if pending > 0 or depth > 0:
                meta.append(line)
                pending, depth = consume_macro_args(line, pending, depth)
            elif (mm := META_RE.match(line)):
                meta.append(line)
                pending, depth = consume_macro_args(mm.group(2), META_ARITY[mm.group(1)], 0)
                m = LEAN_BIND_RE.match(line)
                if m:
                    for part in m.group(1).split(","):
                        part = part.strip()
                        if part and not part.startswith("["):
                            bindings.append(part)
            else:
                prose.append(line)
            i += 1
        #: A grouped environment documents every one of its declarations, so its
        #: body carries each cached statement in turn -- one paragraph per
        #: declaration -- rather than the first one's claim standing in for all.
        group = [b for b in bindings if b in entries]
        binding = group[0] if group else (bindings[0] if bindings else None)
        end_line = lines[i] if i < len(lines) else r"\end{theorem}"
        entry = entries.get(binding) if binding else None
        if entry and len(group) > 1:
            unsafe = [b for b in group if not Q.typesets(entries[b].get("statement", ""))]
            if unsafe:
                for b in unsafe:
                    report.append((tex.name, b, "latex-unsafe"))
                entry = None
            else:
                entry = dict(entry)
                entry["statement"] = "\n\n".join(
                    entries[b]["statement"].strip() for b in group
                )
                entry["title"] = ""          # keep the group's own title
                for b in group[1:]:
                    entries[b].setdefault("replaced", "\n".join(prose))
                    cache.cache_path(b).write_text(
                        json.dumps(entries[b], ensure_ascii=False, indent=1) + "\n",
                        encoding="utf-8",
                    )
                    report.append((tex.name, b, "applied"))
        if entry and not Q.typesets(entry.get("statement", "")):
            # A statement that will not typeset must never reach the document.
            report.append((tex.name, binding, "latex-unsafe"))
            if "replaced" in entry:
                # This entry was applied by an earlier run; put the blueprint's
                # own prose back rather than leaving the bad statement behind.
                prose = entry["replaced"].split("\n")
                report.append((tex.name, binding, "reverted"))
            entry = None
        out.extend(meta)
        if entry and entry.get("statement"):
            if "replaced" not in entries[binding]:
                entries[binding]["replaced"] = "\n".join(prose)
                path = cache.cache_path(binding)
                path.write_text(
                    json.dumps(entries[binding], ensure_ascii=False, indent=1) + "\n",
                    encoding="utf-8",
                )
            out.append(wrap(entry["statement"].strip()))
            changed = True
            new_title = safe_title(entry.get("title", ""))
            if span and new_title:
                out[begin_idx] = begin_line[:span[0]] + new_title + begin_line[span[1]:]
            elif span and entry.get("title"):
                report.append((tex.name, binding, "title-unsafe"))
            report.append((tex.name, binding, "applied"))
        else:
            out.extend(prose)
        out.append(end_line)
        i += 1
    return "\n".join(out) + "\n" if changed else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true", help="report only, write nothing")
    ap.add_argument("--no-apply", action="store_true",
                    help="skip the regenerated-statement stage")
    ap.add_argument("--apply-only", action="store_true",
                    help="skip the docstring stage")
    args = ap.parse_args()

    report: list = []
    for tex in sorted(() if args.apply_only else TEX_DIR.glob("*.tex")):
        lean = LEAN_DIR / (tex.stem + ".lean")
        if not lean.exists():
            print(f"  !! no Lean module for {tex.name}")
            continue
        new = rewrite_file(tex, docstrings(lean), report)
        if new is None:
            print(f"  -- {tex.name}: unchanged")
            continue
        if args.check:
            print(f"  ~~ {tex.name}: would rewrite")
        else:
            tex.write_text(new, encoding="utf-8")
            print(f"  ok {tex.name}: rewritten")

    if not args.no_apply:
        entries = cache.load_all()
        print(f"\n{len(entries)} regenerated statements cached")
        for tex in sorted(CHAPTER_DIR.rglob("*.tex")):
            new = apply_cached(tex, entries, report)
            if new is None:
                continue
            if args.check:
                print(f"  ~~ {tex.name}: would apply")
            else:
                tex.write_text(new, encoding="utf-8")

    kinds: dict[str, int] = {}
    for _, _, k in report:
        kinds[k] = kinds.get(k, 0) + 1
    print("\nsummary:", kinds)
    for name, binding, kind in report:
        if kind in ("no-docstring", "empty-statement", "title-unsafe",
                    "latex-unsafe", "reverted"):
            print(f"  {kind}: {name} {binding}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
