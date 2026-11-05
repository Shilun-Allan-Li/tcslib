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
merges the new records into `dataset/tcslib_theorems.jsonl.gz`.  It only
touches what changed, asks before each paid step unless `--yes`, and resumes if
interrupted.  `--modules <YourModule>` limits it to your records.

Then commit what it changed: the blueprint `.tex` files, everything under
`blueprint/src/references/`, and `dataset/tcslib_theorems.jsonl.gz`.

## What you need on the machine

- Python 3.10+ (standard library only).
- The Lean toolchain (`elan`) and one `lake build`.
- The Claude Code CLI (`claude`) or the OpenAI Codex CLI (`codex`), logged in; the spend
  lands on that account.  `--backend codex --model gpt-5` switches vendor.
- For PDFs: `pdf2txt.py` (pdfminer.six) and Ghostscript.

`--check-env` lists what is missing.  The full description of every stage, flag and
column is in `dataset/README.md`.
