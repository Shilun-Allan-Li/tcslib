# Adding your formalization to the dataset

Two steps after you formalize something.  Everything else is automatic.

## 1. Attach the text you formalized from

If the paper or chapter is not already under `blueprint/src/references/`, copy it there:

```bash
cp ~/texts/arora-barak-ch09.pdf blueprint/src/references/
```

Your docstrings already cite it by tag (`[AB09, Thm 9.3]`, policy.md §2).  A PDF is
enough; the pipeline turns it into a validated `<name>.md` and learns which tag it
covers from the theorems it ends up citing.  To state the tag yourself, use
`--source AB09=~/texts/arora-barak-ch09.pdf` in step 2 instead of copying.

`python3 scripts/sources.py` shows which texts are attached, which theorems each one is
cited for, and which tags still have no text.

## 2. Run the pipeline

```bash
python3 scripts/dataset_pipeline.py --check-env    # once per machine
python3 scripts/dataset_pipeline.py --estimate     # what it would do, and the cost
python3 scripts/dataset_pipeline.py --build --yes  # do it
```

The run builds the library (`--build`), gives every new declaration a blueprint entry,
matches every attached text the blueprint does not cite yet against the dataset, writes
an informal statement for every declaration whose statement no text states and a proof
note for every one whose proof no text proves (a cited passage is used verbatim
instead), rates every proof, and
merges the new records into the local complete JSONL and gzip mirrors, then writes
verified gzip shards (at most 80 MiB each) with `dataset/tcslib_theorems.manifest.json`.  It only
touches what changed, asks before each paid step unless `--yes`, and resumes if
interrupted.  `--modules <YourModule>` limits it to your records.

Then commit what it changed: the blueprint `.tex` files, everything under
`blueprint/src/references/`, the manifest, and its `dataset/shards/` files. The complete compressed local mirror
is retained at `dataset/local/tcslib_theorems.jsonl.gz`.

## Including a separately compiled project

Keep the other project in its own checkout and compile it with its own pinned
toolchain. Register its original module root and refresh the graph from the existing
artifacts, without adding it as a TCSlib dependency:

```bash
python3 scripts/dataset_pipeline.py --project-root FABL=../FABL --check-env
python3 scripts/dataset_pipeline.py --refresh-graph --estimate
python3 scripts/dataset_pipeline.py --refresh-graph --yes \
    --source OD14=/path/to/Analysis-of-Boolean-Functions.pdf
```

The registration is saved in `dataset/projects.json`; paths are relative to this
repository. Repeat `--project-root NAME=PATH` to add another project or relocate a
checkout. Subsequent runs retain the registration. `--modules FABL` selects just its
records, and the dataset stage merges them into the existing dataset. `--build`
builds TCSlib only; `--refresh-graph` reads all registered projects' existing `.ilean`
files. Neither changes a toolchain or dependency. A registered checkout must remain
available when regenerating its records.

Records retain their upstream module names and carry a `provenance` object naming
the project, commit, repository, Lean toolchain, dependency-manifest hash, license
hash, and source-file hash. A FABL record must be checked using FABL's environment;
its inclusion does not imply compatibility with TCSlib's Lean version. The
`proof_complete` flag remains a textual `sorry` check, not compilation evidence.

Use `--backend codex --model <available-model>` if Claude Code is unavailable. The
model must meet the pipeline's quality floor and be available to the logged-in account.

## What you need on the machine

- Python 3.10+ (standard library only).
- The Lean toolchain (`elan`) and one `lake build`.
- The Claude Code CLI (`claude`) or the OpenAI Codex CLI (`codex`), logged in; the spend
  lands on that account.  `--backend codex --model gpt-6-luna` selects Codex with Luna.
- For PDFs: `pdf2txt.py` (pdfminer.six) and Ghostscript.

`--check-env` lists what is missing.  The full description of every stage, flag and
column is in `dataset/README.md`.