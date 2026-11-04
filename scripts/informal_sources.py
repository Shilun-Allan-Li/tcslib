"""
The informal half of a dataset record: `informal_statement` / `statement_source` and
`informal_proof` / `proof_source`.

The statement and the proof are two columns, each with its own origin marker:

    informal_statement   the result in prose.
      statement_source   `citation`  the blueprint entry carries `\\statementsource`:
                                     the passage of the reference document that states
                                     the result, verbatim from the validated text under
                                     blueprint/src/references/<doc>.md;
                         `lean`      otherwise: prose written from the Lean declaration
                                     (the blueprint entry's statement, with the
                                     definitions it relies on).
    informal_proof       the proof in prose, or "" when there is none.
      proof_source       `citation`  the entry carries `\\proofsource`: the passage that
                                     proves the result, verbatim;
                         `lean`      otherwise, when blueprint/src/references/informalized/
                                     <name>.md holds a note: the informalized account of
                                     the Lean proof;
                         `none`      neither.

A citation wins in each column independently: a record whose only citation is a
`\\proofsource` keeps its Lean-derived statement and takes the cited proof.  Nothing is
generated here: this module only reads what the blueprint, the reference texts and the
notes already hold.  It is used by build_dataset.py at build time and runnable on its own
to rewrite the informal half of an existing dataset from those same files (a repair, or
the migration from an older schema -- the one-column `informal_statement` /
`informal_source` layout, or the older `statement_informal` / `proof_notes` one):

    python3 scripts/informal_sources.py                    # rewrite the dataset in place
    python3 scripts/informal_sources.py --out FILE         # write elsewhere
    python3 scripts/informal_sources.py --dry-run          # report only, write nothing

A citation that can no longer be resolved to text (document or block missing from
references/) is reported and the column falls back to its Lean-derived value.  On its own
this script cannot rebuild the Lean-derived statement of a record whose statement is
currently a citation; such a record whose citation was removed keeps its text and is
reported -- rebuild it with build_dataset.py.
"""

from __future__ import annotations

import argparse
import gzip
import json
import re
import shutil
import sys
from collections import Counter
from pathlib import Path
from typing import NamedTuple

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.blueprint import ENV_RE, parse_proof_sources  # noqa: E402
from proofmatch.dataset_io import dataset_exists, read_dataset_text  # noqa: E402

CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
REFERENCES_DIR = BASE / "blueprint" / "src" / "references"
INFORMALIZED_DIR = REFERENCES_DIR / "informalized"
DEFAULT_DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"

LEAN_ANY_RE = re.compile(r"\\lean\{([^}]*)\}")

#: The values of `statement_source` and of `proof_source`.
STATEMENT_SOURCES = ("citation", "lean")
PROOF_SOURCES = ("citation", "lean", "none")
#: The four informal columns, in the order they sit in a record (right after `id`).
COLUMNS = ("informal_statement", "statement_source", "informal_proof", "proof_source")
#: In a `lean` statement with a definitions block, the claim follows this label.
STATEMENT_LABEL = "\n\nStatement: "
#: Columns of the schemas this module replaced; dropped when a record is rewritten.
#: `informal_source` is the one-column schema (statement and proof account in one
#: `informal_statement`, joined by `PROOF_SEP`); the others are the schema before that.
PROOF_SEP = "\n\nProof: "
LEGACY_COLUMNS = ("informal_source", "statement_informal", "proof_sources",
                  "proof_steps", "proof_notes")


class Informal(NamedTuple):
    statement: str
    statement_source: str
    proof: str
    proof_source: str
    #: (document, block) pairs cited by the entry but absent from references/<doc>.md.
    unresolved: list[tuple[str, str]]


# ---------------------------------------------------------------- the sources

def blueprint_citations() -> dict[str, dict[str, list[dict]]]:
    """lean name -> {proof_sources, statement_sources, tex}, read from the blueprint."""
    out: dict[str, dict[str, list[dict]]] = {}
    for tex in sorted(CHAPTER_DIR.rglob("*.tex")):
        text = tex.read_text(encoding="utf-8", errors="ignore")
        for env_match in ENV_RE.finditer(text):
            env = env_match.group(0)
            names = [
                name.strip()
                for m in LEAN_ANY_RE.finditer(env)
                for name in m.group(1).split(",")
                if name.strip()
            ]
            if not names:
                continue
            proofs = parse_proof_sources(env, "proofsource")
            statements = parse_proof_sources(env, "statementsource")
            for name in names:
                entry = out.setdefault(
                    name, {"proof_sources": [], "statement_sources": [], "tex": []}
                )
                rel = tex.relative_to(CHAPTER_DIR).as_posix()
                if rel not in entry["tex"]:
                    entry["tex"].append(rel)
                for key, parsed in (
                    ("proof_sources", proofs),
                    ("statement_sources", statements),
                ):
                    for source in parsed.get(name, ()):
                        row = {
                            "document": source.document,
                            "blocks": list(source.blocks),
                        }
                        if row not in entry[key]:
                            entry[key].append(row)
    return out


def cites_statement(lean_name: str, citations: dict) -> bool:
    """The entry carries a `\\statementsource` (its statement column is the passage)."""
    return bool((citations.get(lean_name) or {}).get("statement_sources"))


def cites_proof(lean_name: str, citations: dict) -> bool:
    """The entry carries a `\\proofsource` (its proof column is the passage)."""
    return bool((citations.get(lean_name) or {}).get("proof_sources"))


def is_cited(lean_name: str, citations: dict) -> bool:
    """The entry carries a citation of either kind."""
    return cites_statement(lean_name, citations) or cites_proof(lean_name, citations)


def load_block_text() -> dict[str, dict[str, str]]:
    """document -> {block_id: block markdown}, for every validated reference."""
    out: dict[str, dict[str, str]] = {}
    for md in sorted(REFERENCES_DIR.glob("*.md")):
        if md.name.endswith(".raw.md"):
            continue
        text = md.read_text(encoding="utf-8", errors="ignore")
        anchors = list(re.finditer(r'<a id="([^"]+)"></a>', text))
        blocks: dict[str, str] = {}
        for index, anchor in enumerate(anchors):
            end = anchors[index + 1].start() if index + 1 < len(anchors) else len(text)
            body = text[anchor.end() : end]
            # Drop the provenance comment; keep the mathematical prose.
            body = re.sub(r"<!--.*?-->", "", body, flags=re.S).strip()
            blocks[anchor.group(1)] = body
        out[md.stem] = blocks
    return out


def load_notes() -> dict[str, tuple[Path, str]]:
    """lean name (casefolded) -> (path, markdown) for each informalized note.

    Keys are casefolded because this filesystem is case-insensitive: a structure and its
    lowercase constructor-style def cannot own separate files, so one note may document
    both and must be findable under either name.
    """
    out: dict[str, tuple[Path, str]] = {}
    if not INFORMALIZED_DIR.exists():
        return out
    # Non-recursive on purpose: notes rejected as tactic transcripts are parked under
    # INFORMALIZED_DIR/rejected/ (see informalize_proofs.py) and must not be picked up.
    for md in sorted(INFORMALIZED_DIR.glob("*.md")):
        if md.stem == "WORKLIST":
            continue
        out[md.stem.casefold()] = (md, md.read_text(encoding="utf-8", errors="ignore"))
    return out


def note_for(lean_name: str, notes: dict[str, tuple[Path, str]]):
    for key in (lean_name.casefold(), lean_name.rsplit(".", 1)[-1].casefold()):
        if key in notes:
            return notes[key]
    # The earliest notes were filed under a *module*-qualified name
    # (`QuantumSingleton.dist_implies_correctable.md`) while the Lean declaration is
    # root-namespaced (`dist_implies_correctable`), so neither key above matches. Fall
    # back to a note whose stem ends with `.<lean_name>`, which recovers those without
    # letting a bare suffix collide with an unrelated declaration.
    suffix = "." + lean_name.casefold()
    matches = [value for key, value in notes.items() if key.endswith(suffix)]
    if len(matches) == 1:
        return matches[0]
    return None


# ---------------------------------------------------------------- the columns

def cited_texts(
    lean_name: str, citations: dict, block_text: dict[str, dict[str, str]], key: str
) -> tuple[list[str], list[tuple[str, str]]]:
    """(text of every block the entry cites under `key`, in order; (document, block)
    pairs with no text).  `key` is `statement_sources` or `proof_sources`; a block cited
    twice appears once."""
    rows = (citations.get(lean_name) or {}).get(key) or []
    texts: list[str] = []
    unresolved: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for row in rows:
        by_id = block_text.get(row["document"], {})
        for block in row["blocks"]:
            pair = (row["document"], block)
            if pair in seen:
                continue
            seen.add(pair)
            text = (by_id.get(block) or "").strip()
            if text:
                texts.append(text)
            else:
                unresolved.append(pair)
    return texts, unresolved


def note_body(markdown: str) -> str:
    """The proof account of an informalized note, as the `informal_proof` column.

    Drops the provenance comments and the title heading, and -- when the note has the
    generated `**Claim.** ... **Proof.** ...` shape -- the claim paragraph, since the
    statement it restates is the record's `informal_statement`.  Everything else is kept
    verbatim.
    """
    body = re.sub(r"<!--.*?-->", "", markdown, flags=re.S).strip()
    body = re.sub(r"^#+ .*\n?", "", body, count=1).strip()
    if "**Proof.**" in body:
        body = re.sub(r"\*\*Claim\.\*\*.*?(?=\n\n|\Z)", "", body, count=1, flags=re.S).strip()
        if body.startswith("**Proof.**"):
            body = body[len("**Proof.**"):].lstrip()
    return re.sub(r"\n{3,}", "\n\n", body).strip()


# ---------------------------------------------------------------- quality gates

#: Tactic names whose appearance in a proof account marks a tactic transcript rather
#: than a mathematical argument (the audit class "sketch quotes the formal proof").
TACTIC_RE = re.compile(
    r"\b(simp|simp_all|simpa|rw|rwa|exact|refine|intro|intros|obtain|rcases|rintro|"
    r"omega|linarith|nlinarith|positivity|norm_num|ring|ring_nf|field_simp|apply|"
    r"constructor|use|calc|cases|induction|unfold|subst|ext|funext|congr|aesop|decide|"
    r"push_cast|norm_cast|gcongr|specialize|exact_mod_cast|by_cases|split|split_ifs|"
    r"contradiction|exfalso|trivial|rfl|infer_instance|mono|bound)\b"
)
CODE_RE = re.compile(r"```[\s\S]*?```|`[^`\n]*`")
#: A proof account is a transcript when more than this share of its proof section is
#: backticked code and it names at least this many tactics.
TRANSCRIPT_CODE_FRACTION = 0.5
TRANSCRIPT_TACTICS = 3


def proof_section(account: str) -> str:
    """The argument itself: the account up to its `**Used in.**` / `**Key facts.**` /
    `**Caveat.**` trailer."""
    return re.split(r"\n\*\*(Used in|Key facts|Caveat)\.\*\*", account)[0]


def transcript_score(account: str) -> tuple[float, int]:
    """(share of the proof section inside backticks, number of tactic names in it)."""
    body = proof_section(account)
    code = CODE_RE.findall(body)
    fraction = sum(len(c) for c in code) / max(1, len(body))
    tactics = len(TACTIC_RE.findall(body))
    return fraction, tactics


def is_tactic_transcript(account: str) -> bool:
    """A `lean` proof account that narrates the tactic script instead of the
    mathematics: mostly code, with several tactic names.  Such an account is no
    informal proof (it restates the `proof` column) and is rejected."""
    fraction, tactics = transcript_score(account)
    return fraction > TRANSCRIPT_CODE_FRACTION and tactics >= TRANSCRIPT_TACTICS


def informal_columns(
    lean_name: str,
    lean_prose: str,
    citations: dict,
    block_text: dict[str, dict[str, str]],
    notes: dict[str, tuple[Path, str]],
) -> Informal:
    """The four informal columns of one record.

    `lean_prose` is the Lean-derived statement (build_dataset.py's composition of the
    blueprint entry and its definitions); it is the statement when no `\\statementsource`
    resolves to text.
    """
    stmt_texts, unresolved = cited_texts(lean_name, citations, block_text, "statement_sources")
    proof_texts, missing = cited_texts(lean_name, citations, block_text, "proof_sources")
    unresolved += missing
    if stmt_texts:
        statement, statement_source = "\n\n".join(stmt_texts), "citation"
    else:
        statement, statement_source = lean_prose, "lean"
    if proof_texts:
        proof, proof_source = "\n\n".join(proof_texts), "citation"
    else:
        proof, proof_source = "", "none"
        found = note_for(lean_name, notes)
        if found is not None:
            body = note_body(found[1])
            if body:
                proof, proof_source = body, "lean"
    return Informal(statement, statement_source, proof, proof_source, unresolved)


def statement_part(informal: str) -> str:
    """The claim alone of a `lean` informal statement, without the definitions block
    that may precede it."""
    text = informal.split(PROOF_SEP, 1)[0]   # tolerate the one-column schema
    if text.startswith("Definitions:"):
        label = text.find(STATEMENT_LABEL)
        if label >= 0:
            text = text[label + len(STATEMENT_LABEL):]
    return text


def place_columns(record: dict, informal: Informal) -> dict:
    """Rebuild `record` with the informal columns right after `id` and no legacy column."""
    out: dict = {
        "id": record["id"],
        "informal_statement": informal.statement,
        "statement_source": informal.statement_source,
        "informal_proof": informal.proof,
        "proof_source": informal.proof_source,
    }
    for key, value in record.items():
        if key in out or key in LEGACY_COLUMNS:
            continue
        out[key] = value
    return out


# ---------------------------------------------------------------- standalone

def lean_prose_of(record: dict) -> str | None:
    """The Lean-derived statement an existing record holds, or None when it has been
    replaced by a citation and cannot be recovered without a rebuild."""
    if "statement_informal" in record:
        # Oldest schema: `informal_statement` is the blueprint composition itself.
        return record.get("informal_statement") or ""
    if "informal_source" in record:
        # One-column schema: statement and proof account in one field; a `citation`
        # record held the cited passage(s) only.
        if record["informal_source"] == "lean":
            return (record.get("informal_statement") or "").split(PROOF_SEP, 1)[0]
        return None
    if record.get("statement_source") == "lean":
        return record.get("informal_statement") or ""
    return None


def _display(path: Path) -> str:
    try:
        return path.relative_to(BASE).as_posix()
    except ValueError:
        return str(path)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    if not dataset_exists(args.dataset):
        print(f"ERROR: {args.dataset} not found.")
        return 1

    print("Reading blueprint citations ...")
    citations = blueprint_citations()
    print(f"  {len(citations)} blueprint-bound declarations")
    block_text = load_block_text()
    print(f"  {len(block_text)} reference documents, "
          f"{sum(len(v) for v in block_text.values())} blocks indexed")
    notes = load_notes()
    print(f"  {len(notes)} informalized notes")

    records = [
        json.loads(line)
        for line in read_dataset_text(args.dataset).splitlines()
        if line.strip()
    ]
    print(f"  {len(records)} dataset records\n")

    stmt_sources: Counter[str] = Counter()
    proof_sources: Counter[str] = Counter()
    unresolved: list[tuple[str, str, str]] = []
    stuck: list[str] = []
    updated = []
    for record in records:
        lean_name = str(record.get("lean_name") or record.get("id") or "")
        prose = lean_prose_of(record)
        if prose is None:
            # The statement is a citation and the Lean prose is gone: recompute the
            # citation; if it no longer resolves, keep the text and report.
            texts, _ = cited_texts(lean_name, citations, block_text, "statement_sources")
            if not texts:
                stuck.append(lean_name)
            prose = record.get("informal_statement") or ""
        informal = informal_columns(lean_name, prose, citations, block_text, notes)
        unresolved += [(lean_name, d, b) for d, b in informal.unresolved]
        stmt_sources[informal.statement_source] += 1
        proof_sources[informal.proof_source] += 1
        updated.append(place_columns(record, informal))

    print("statement_source:")
    for source, count in stmt_sources.most_common():
        print(f"  {count:5d}  {source}")
    print("proof_source:")
    for source, count in proof_sources.most_common():
        print(f"  {count:5d}  {source}")
    if unresolved:
        print(f"\nCitations whose blocks are missing from the reference .md: {len(unresolved)}")
        for lean_name, document, block in unresolved[:10]:
            print(f"  {lean_name} -> {document}: {block}")
        if len(unresolved) > 10:
            print(f"  ... and {len(unresolved) - 10} more")
    if stuck:
        print(f"\nRecords whose statement citation is gone but whose Lean prose cannot be "
              f"recovered here (rebuild with build_dataset.py): {len(stuck)}")
        for lean_name in stuck[:10]:
            print(f"  {lean_name}")

    if args.dry_run:
        print("\n--dry-run: nothing written.")
        return 0

    out_path = (args.out or args.dataset).resolve()
    with out_path.open("w", encoding="utf-8") as handle:
        for record in updated:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
    print(f"\nWrote {len(updated)} records -> {_display(out_path)}")

    # The theorems viewer fetches the gzipped copy in preference to the .jsonl, so
    # rewriting only the .jsonl would leave the site serving the old columns.
    gz_path = out_path.with_suffix(out_path.suffix + ".gz")
    gz_tmp = gz_path.with_suffix(gz_path.suffix + ".tmp")
    with open(out_path, "rb") as src, gzip.open(gz_tmp, "wb", compresslevel=9) as dst:
        shutil.copyfileobj(src, dst)
    gz_tmp.replace(gz_path)
    print(f"Refreshed gzip copy -> {_display(gz_path)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
