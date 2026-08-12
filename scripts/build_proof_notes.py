"""
Attach a `proof_notes` entry to every dataset record, immediately before `proof`.

Companion to build_dataset.py. That script emits the statement, the upstream definitions
and the flattened proof file; it also records `\\proofsource` citations, but it drops
`\\statementsource` entirely and knows nothing about the informalized notes under
blueprint/src/references/informalized/. So a record could carry a fully-written human
account of its proof and show no trace of it.

This script closes that gap. For every record it collects whatever human-readable account
of the proof exists, from three places, and folds them into one `proof_notes` object:

    * `\\proofsource{doc}{blocks}`     -- the document *proves* this result
    * `\\statementsource{doc}{blocks}` -- the document *states* it (different proof, or
                                          it is cited there as a black box)
    * informalized/<lean_name>.md      -- no citation exists, so the Lean proof itself was
                                          informalized into prose

Citations are resolved to the actual block text from blueprint/src/references/<doc>.md, so
the field is self-contained in the same spirit as `informal_statement` -- a consumer never
has to go and re-open the source document.

`proof_notes` is inserted directly before `proof` so a reader meets the informal account of
the proof before the formal one. Records with no citation and no note get
`"proof_notes": null` rather than being dropped or silently skipped.

Usage:
    python3 scripts/build_proof_notes.py                     # rewrite the dataset in place
    python3 scripts/build_proof_notes.py --out FILE          # write elsewhere
    python3 scripts/build_proof_notes.py --dry-run           # report only, write nothing
    python3 scripts/build_proof_notes.py --no-block-text     # citations without block prose
"""

import argparse
import gzip
import json
import re
import shutil
import sys
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
ANCHOR_TMPL = '<a id="{block}"></a>'


def blueprint_citations() -> dict[str, dict[str, list[dict]]]:
    """lean name -> {proof_sources, statement_sources}, read from the blueprint."""
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


def build_proof_notes(
    lean_name: str,
    citations: dict,
    block_text: dict[str, dict[str, str]],
    notes: dict,
    *,
    include_block_text: bool,
):
    cited = citations.get(lean_name) or {}
    proof_sources = cited.get("proof_sources") or []
    statement_sources = cited.get("statement_sources") or []
    found_note = note_for(lean_name, notes)

    if not proof_sources and not statement_sources and not found_note:
        return None, "none"

    def decorate(rows: list[dict]) -> list[dict]:
        out = []
        for row in rows:
            item = {"document": row["document"], "blocks": list(row["blocks"])}
            if include_block_text:
                by_id = block_text.get(row["document"], {})
                item["block_text"] = [
                    {"block": block, "text": by_id.get(block, "")}
                    for block in row["blocks"]
                ]
                item["unresolved_blocks"] = [
                    block for block in row["blocks"] if block not in by_id
                ]
            out.append(item)
        return out

    if proof_sources:
        kind = "proof_citation"
    elif statement_sources:
        kind = "statement_citation"
    else:
        kind = "informalized"
    if found_note and (proof_sources or statement_sources):
        kind += "+informalized"

    payload = {
        "kind": kind,
        "proof_sources": decorate(proof_sources),
        "statement_sources": decorate(statement_sources),
        "informalized": None,
    }
    if found_note:
        path, markdown = found_note
        payload["informalized"] = {
            "path": path.relative_to(BASE).as_posix(),
            "markdown": markdown,
        }
    return payload, kind


def insert_before(record: dict, key: str, value, before: str) -> dict:
    """Rebuild the record so `key` lands immediately before `before`."""
    out: dict = {}
    placed = False
    for name, existing in record.items():
        if name == key:
            continue
        if name == before and not placed:
            out[key] = value
            placed = True
        out[name] = existing
    if not placed:
        out[key] = value
    return out


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--dataset", type=Path, default=DEFAULT_DATASET)
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-block-text", action="store_true")
    args = ap.parse_args()

    if not dataset_exists(args.dataset):
        print(f"ERROR: {args.dataset} not found.")
        return 1

    print("Reading blueprint citations ...")
    citations = blueprint_citations()
    print(f"  {len(citations)} blueprint-bound declarations")
    block_text = {} if args.no_block_text else load_block_text()
    if block_text:
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

    from collections import Counter

    kinds = Counter()
    unresolved = []
    updated = []
    for record in records:
        lean_name = str(record.get("lean_name") or record.get("id") or "")
        payload, kind = build_proof_notes(
            lean_name,
            citations,
            block_text,
            notes,
            include_block_text=not args.no_block_text,
        )
        kinds[kind] += 1
        if payload:
            for group in ("proof_sources", "statement_sources"):
                for row in payload[group]:
                    if row.get("unresolved_blocks"):
                        unresolved.append((lean_name, row["document"], row["unresolved_blocks"]))
        updated.append(insert_before(record, "proof_notes", payload, "proof"))

    covered = len(records) - kinds["none"]
    print("proof_notes coverage:")
    for kind, count in kinds.most_common():
        print(f"  {count:5d}  {kind}")
    print(f"\n  {covered}/{len(records)} records carry a proof note "
          f"({100 * covered / max(len(records), 1):.1f}%)")

    if unresolved:
        print(f"\nCitations whose blocks are missing from the reference .md: "
              f"{len(unresolved)}")
        for lean_name, document, blocks in unresolved[:10]:
            print(f"  {lean_name} -> {document}: {', '.join(blocks)}")
        if len(unresolved) > 10:
            print(f"  ... and {len(unresolved) - 10} more")

    if args.dry_run:
        print("\n--dry-run: nothing written.")
        return 0

    out_path = args.out or args.dataset
    with out_path.open("w", encoding="utf-8") as handle:
        for record in updated:
            handle.write(json.dumps(record, ensure_ascii=False) + "\n")
    print(f"\nWrote {len(updated)} records -> {out_path.relative_to(BASE)}")

    # The theorems viewer fetches the gzipped copy in preference to the .jsonl, so
    # rewriting only the .jsonl would leave the site serving records with no
    # `proof_notes` at all. Refresh it here for the same reason build_dataset does.
    gz_path = out_path.with_suffix(out_path.suffix + ".gz")
    gz_tmp = gz_path.with_suffix(gz_path.suffix + ".tmp")
    with open(out_path, "rb") as src, gzip.open(gz_tmp, "wb", compresslevel=9) as dst:
        shutil.copyfileobj(src, dst)
    gz_tmp.replace(gz_path)
    print(f"Refreshed gzip copy -> {gz_path.relative_to(BASE)}")
    keys = list(updated[0].keys())
    print(f"key order around the insert: "
          f"{keys[max(0, keys.index('proof_notes') - 1):keys.index('proof_notes') + 2]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
