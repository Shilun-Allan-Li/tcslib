import VersoBlog

open Verso Genre
open Blog hiding lean
open Site

#doc (Page) "Dataset" =>

::::htmlDiv (class := "page-title")

TCSlib theorem dataset

A comprehensive set of theorems of theoretical computer science formalized in
Lean 4, one record per theorem of the library, with the informal statement, the formal
statement, the proof, and where the mathematics came from.

::::

# What it is

Every theorem and lemma of TCSlib that has a blueprint entry is one record. A record pairs:

* an informal statement in prose: the passage of the source text that states or proves the
  result, or, when no text cites it, prose written from the Lean with the definitions it
  relies on and an account of the proof;
* a standalone formal statement: a Lean 4 file that ends with the declaration, its proof
  replaced by `sorry`, carrying the definitions, instances and context the statement needs;
* the proof: a second Lean 4 file with the declaration proved for real and its whole
  dependency closure within the library flattened into it, so it compiles with Mathlib alone;
* a difficulty rating of the Lean proof script, from 1 to 7;
* where the informal statement came from: the paper or textbook chapter the result was
  formalized from, or, when no such text was attached, the Lean itself.

The set is **mixed**:

* **Some proofs are still open.** When the proof, or the proof of something it depends on,
  still contains `sorry`, the record's `proof_complete` is false. In the deployed build
  (%%build_date_text%%) that is %%n_sorry%% of %%n_records%% records.
* **Not every record cites a text.** `informal_source` is `citation` for the %%n_cited%%
  records whose informal statement is the passage of a source document that states or proves
  the result, and `lean` for the %%n_lean%% whose text was written from the Lean instead,
  because the text they were formalized from was never attached: the statement by the
  blueprint's author or by a language model checked against a rubric, followed for
  %%n_lean_with_proof%% of them by an informalized account of the Lean proof. The remaining
  %%n_lean_without_proof%% have no proof account yet.

The set is still growing. It is rebuilt incrementally from the library, so each build adds the
newly formalized declarations and the counts above change. View a visualization of the
repository at [theorem viewer](/tcslib/theorems/).

By area in the deployed build: %%by_area%%.

The numbers on this page are computed from the dataset file this site serves, each time
the site is deployed.

# How to download it

The dataset is one gzipped JSON Lines file, about %%size_mb%% MB, one JSON object per line.

:::::htmlDiv (class := "download-buttons")

::::html a (class := "hero-btn primary") (href := "/tcslib/theorems/tcslib_theorems.jsonl.gz") (download := "tcslib_theorems.jsonl.gz")
:::html img (src := "/tcslib/static/arrow.svg") (alt := "") (width := "20") (height := "20")
:::
Download tcslib_theorems.jsonl.gz
::::

::::html a (class := "hero-btn secondary") (href := "https://huggingface.co/datasets/Hydroxyi/TCSlib")
Hugging Face
::::

:::::

The button serves the build that is deployed with this site. The same file is also:

* [`dataset/tcslib_theorems.jsonl.gz`](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/tcslib_theorems.jsonl.gz)
  in the repository, where every build is a commit;
* [`Hydroxyi/TCSlib`](https://huggingface.co/datasets/Hydroxyi/TCSlib) on Hugging Face,
  for `datasets.load_dataset`.

In Python:

```
import gzip, json

with gzip.open("tcslib_theorems.jsonl.gz", "rt") as f:
    records = [json.loads(line) for line in f]

complete = [r for r in records if r["proof_complete"]]
cited = [r for r in records if r["informal_source"] == "citation"]
```

The `proof` column of a complete record compiles in a project that depends on the same
Mathlib version as the library (`lake-manifest.json` in the repository pins it). The
`formal_statement` column reproduces the declaration's environment as faithfully as a
flattener can; the builder measures the compile rate of a sample on every run.

# Columns

* `id`, `lean_name`: the fully qualified Lean name, which is the record key.
* `informal_statement`, `informal_source`, `title`, `definitions`: the informal half;
  `informal_source` is `citation` or `lean`.
* `formal_statement`, `upstream_defs`, `n_upstream_defs`: the formal statement and the
  definitions it carries.
* `source_module`, `kind`: the Lean module; `theorem` or `lemma`.
* `difficulty`: integer 1 to 7, or null when unrated.
* `proof`, `proof_upstream_decls`, `n_proof_upstream_decls`, `proof_unresolved_deps`,
  `proof_complete`: the proof file, what it carries, and whether it is finished.

# Where it comes from

The records are derived from the library and its blueprint by the pipeline in the
repository's [`dataset/`](https://github.com/Shilun-Allan-Li/tcslib/tree/main/dataset)
directory. Whoever formalizes a result attaches the text it came from and runs the
pipeline; the pipeline gives new declarations their entries, statements and ratings,
matches attached texts against the dataset, and merges the new records. It never
searches for sources itself, which is why some records cite a text and others do not.

The dataset is distributed with the library under the Apache 2.0 license. Corrections and
questions go to the [issue tracker](https://github.com/Shilun-Allan-Li/tcslib/issues).
