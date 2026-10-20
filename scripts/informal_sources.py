"""
The informal half of a dataset record: `informal_statement` and `informal_source`.

A record's informal statement comes from one of two places, in this order of
preference:

    citation   the blueprint entry cites a reference document (`\\proofsource` or
               `\\statementsource`): the informal statement IS the cited passage,
               taken verbatim from the validated text under
               blueprint/src/references/<doc>.md (statement blocks first, then
               proof blocks, each block once);
    lean       nothing cites it: the prose written from the Lean declaration (the
               blueprint entry's statement, with the definitions it relies on),
               followed by the informalized account of the Lean proof from
               blueprint/src/references/informalized/<name>.md when one exists.

`informal_source` records which.  Nothing is generated here: this module only reads
what the blueprint, the reference texts and the notes already hold.  It is used by
build_dataset.py at build time and runnable on its own to rewrite the informal half of
an existing dataset from those same files (a repair, or the migration from the older
`statement_informal` / `proof_notes` columns):

    python3 scripts/informal_sources.py                    # rewrite the dataset in place
    python3 scripts/informal_sources.py --out FILE         # write elsewhere
    python3 scripts/informal_sources.py --dry-run          # report only, write nothing

A record whose citation can no longer be resolved to text (document or block missing
from references/) falls back to `lean` and is reported.  On its own this script cannot
rebuild the Lean-derived prose of a record that is currently `citation`; a record whose
citation was removed keeps its text and is reported -- rebuild it with build_dataset.py.
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

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))

from proofmatch.blueprint import ENV_RE, parse_proof_sources  # noqa: E402
from proofmatch.dataset_io import dataset_exists, read_dataset_text  # noqa: E402

CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
REFERENCES_DIR = BASE / "blueprint" / "src" / "references"
INFORMALIZED_DIR = REFERENCES_DIR / "informalized"
DEFAULT_DATASET = BASE / "dataset" / "tcslib_theorems.jsonl"

LEAN_ANY_RE = re.compile(r"\\lean\{([^}]*)\}")

#: The two values of `informal_source`.
SOURCES = ("citation", "lean")
#: Separates the statement from the proof account in a `lean` informal statement.
PROOF_SEP = "\n\nProof: "
STATEMENT_LABEL = "\n\nStatement: "
#: Columns of the schema this module replaced; dropped when a record is rewritten.
LEGACY_COLUMNS = ("statement_informal", "statement_source", "proof_sources",
                  "proof_steps", "proof_notes")


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


def is_cited(lean_name: str, citations: dict) -> bool:
    cited = citations.get(lean_name) or {}
    return bool(cited.get("proof_sources") or cited.get("statement_sources"))


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


# ---------------------------------------------------------------- the column

def cited_texts(
    lean_name: str, citations: dict, block_text: dict[str, dict[str, str]]
) -> tuple[list[str], list[tuple[str, str]]]:
    """(text of every cited block, in order; (document, block) pairs with no text).

    Statement citations come first (the passage that states the result), then proof
    citations (the passage that proves it); a block cited twice appears once.
    """
    cited = citations.get(lean_name) or {}
    rows = list(cited.get("statement_sources") or []) + list(cited.get("proof_sources") or [])
    texts: list[str] = []
    unresolved: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for row in rows:
        by_id = block_text.get(row["document"], {})
        for block in row["blocks"]:
            key = (row["document"], block)
            if key in seen:
                continue
            seen.add(key)
            text = (by_id.get(block) or "").strip()
            if text:
                texts.append(text)
            else:
                unresolved.append(key)
    return texts, unresolved


def note_body(markdown: str) -> str:
    """The proof account of an informalized note, ready to follow the statement.

    Drops the provenance comments and the title heading, and -- when the note has the
    generated `**Claim.** ... **Proof.** ...` shape -- the claim paragraph, since the
    statement it restates immediately precedes it.  Everything else is kept verbatim.
    """
    body = re.sub(r"<!--.*?-->", "", markdown, flags=re.S).strip()
    body = re.sub(r"^#+ .*\n?", "", body, count=1).strip()
    if "**Proof.**" in body:
        body = re.sub(r"\*\*Claim\.\*\*.*?(?=\n\n|\Z)", "", body, count=1, flags=re.S).strip()
        if body.startswith("**Proof.**"):
            body = body[len("**Proof.**"):].lstrip()
    return re.sub(r"\n{3,}", "\n\n", body).strip()


def informal_column(
    lean_name: str,
    lean_prose: str,
    citations: dict,
    block_text: dict[str, dict[str, str]],
    notes: dict[str, tuple[Path, str]],
) -> tuple[str, str, list[tuple[str, str]]]:
    """(informal_statement, informal_source, unresolved citation blocks) for one record.

    `lean_prose` is the Lean-derived statement (build_dataset.py's composition of the
    blueprint entry and its definitions); it is used only when nothing cites the record.
    """
    texts, unresolved = cited_texts(lean_name, citations, block_text)
    if texts:
        return "\n\n".join(texts), "citation", unresolved
    found = note_for(lean_name, notes)
    if found is not None:
        body = note_body(found[1])
        if body:
            return lean_prose + PROOF_SEP + body, "lean", unresolved
    return lean_prose, "lean", unresolved


def statement_part(informal: str) -> str:
    """The claim alone of a `lean` informal statement: without the definitions block
    before it and the proof account after it."""
    text = informal.split(PROOF_SEP, 1)[0]
    if text.startswith("Definitions:"):
        label = text.find(STATEMENT_LABEL)
        if label >= 0:
            text = text[label + len(STATEMENT_LABEL):]
    return text


def place_columns(record: dict, informal: str, source: str) -> dict:
    """Rebuild `record` with the informal columns right after `id` and no legacy column."""
    out: dict = {"id": record["id"], "informal_statement": informal, "informal_source": source}
    for key, value in record.items():
        if key in out or key in LEGACY_COLUMNS:
            continue
        out[key] = value
    return out


# ---------------------------------------------------------------- standalone

def lean_prose_of(record: dict) -> str | None:
    """The Lean-derived prose an existing record holds, or None when it has been
    replaced by a citation and cannot be recovered without a rebuild."""
    if any(key in record for key in LEGACY_COLUMNS):
        # Older schema: `informal_statement` is the blueprint composition itself.
        return record.get("informal_statement") or ""
    if record.get("informal_source") == "lean":
        return (record.get("informal_statement") or "").split(PROOF_SEP, 1)[0]
    return None


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

    sources: Counter[str] = Counter()
    with_note = 0
    unresolved: list[tuple[str, str, str]] = []
    stuck: list[str] = []
    updated = []
    for record in records:
        lean_name = str(record.get("lean_name") or record.get("id") or "")
        prose = lean_prose_of(record)
        if prose is None:
            # A `citation` record: recompute the citation; keep the text if it is gone.
            texts, missing = cited_texts(lean_name, citations, block_text)
            unresolved += [(lean_name, d, b) for d, b in missing]
            if texts:
                informal, source = "\n\n".join(texts), "citation"
            else:
                stuck.append(lean_name)
                informal, source = record["informal_statement"], "citation"
        else:
            informal, source, missing = informal_column(lean_name, prose, citations, block_text, notes)
            unresolved += [(lean_name, d, b) for d, b in missing]
            with_note += source == "lean" and PROOF_SEP in informal
        sources[source] += 1
        updated.append(place_columns(record, informal, source))

    print("informal_source:")
    for source, count in sources.most_common():
        print(f"  {count:5d}  {source}")
    print(f"  {with_note:5d}  of the `lean` records carry an informalized proof account")
    if unresolved:
        print(f"\nCitations whose blocks are missing from the reference .md: {len(unresolved)}")
        for lean_name, document, block in unresolved[:10]:
            print(f"  {lean_name} -> {document}: {block}")
        if len(unresolved) > 10:
            print(f"  ... and {len(unresolved) - 10} more")
    if stuck:
        print(f"\nRecords whose citation is gone but whose Lean prose cannot be recovered "
              f"here (rebuild with build_dataset.py): {len(stuck)}")
        for lean_name in stuck[:10]:
            print(f"  {lean_name}")

    if args.dry_run:
        print("\n--dry-run: nothing written.")
        return 0

    out_path = args.out or args.dataset
    with out_path.open("w", encoding="utf-8") as handle:
        for record in updated:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
    print(f"\nWrote {len(updated)} records -> {out_path.relative_to(BASE)}")

    # The theorems viewer fetches the gzipped copy in preference to the .jsonl, so
    # rewriting only the .jsonl would leave the site serving the old columns.
    gz_path = out_path.with_suffix(out_path.suffix + ".gz")
    gz_tmp = gz_path.with_suffix(gz_path.suffix + ".tmp")
    with open(out_path, "rb") as src, gzip.open(gz_tmp, "wb", compresslevel=9) as dst:
        shutil.copyfileobj(src, dst)
    gz_tmp.replace(gz_path)
    print(f"Refreshed gzip copy -> {gz_path.relative_to(BASE)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
