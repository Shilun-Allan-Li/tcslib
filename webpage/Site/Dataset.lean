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

* an informal statement in prose: the passage of the source text that states the result,
  or, when no text states it, prose written from the Lean with the definitions it relies on;
* an informal proof in prose: the passage of the source text that proves the result, or,
  when no text proves it, an account written from the Lean proof;
* a standalone formal statement: a Lean 4 file that ends with the declaration, its proof
  replaced by `sorry`, carrying the definitions, instances and context the statement needs;
* the proof: a second Lean 4 file with the declaration proved for real and its whole
  dependency closure within the library flattened into it, so it compiles with Mathlib alone;
* a difficulty rating of the Lean proof script, from 1 to 7;
* where the informal statement and the informal proof came from: the paper or textbook
  chapter the result was formalized from, or, when no such text was attached, the Lean
  itself.

The set is **mixed**:

* **Some proofs are still open.** When the proof, or the proof of something it depends on,
  still contains `sorry`, the record's `proof_complete` is false. In the deployed build
  (%%build\_date\_text%%) that is %%n\_sorry%% of %%n\_records%% records.
* **Not every record cites a text.** The statement and the proof are cited separately.
  `statement_source` is `citation` for the %%n\_statement\_cited%% records whose informal
  statement is the passage of a source document that states the result, and `lean` for the
  %%n\_statement\_lean%% whose statement was written based on the Lean instead. `proof_source`
  is `citation` for the %%n\_proof\_cited%% records whose informal proof is the passage that
  proves the result, `lean` for the %%n\_proof\_lean%% whose proof is an account written
  from the Lean proof, and `none` for the %%n\_proof\_none%% that have no informal proof yet.
  Writing from the Lean may be due to a variety of reasons, from the statement's status as unwritten common
  knowledge to too specific of a theorem to find in sources, or simply because the source was
  not found.
  

The set is still growing. It is rebuilt incrementally from the library, so each build adds the
newly formalized declarations and the counts above change. View a visualization of the
repository at [theorem viewer](/tcslib/theorems/).

By area in the deployed build: %%by\_area%%.

The numbers on this page are computed from the dataset file this site serves, each time
the site is deployed.

# Attribution

The dataset includes formalizations from
[FABL: Formal Analysis of Boolean Functions in Lean](https://github.com/Polarnova/FABL),
by Asher Yan, formalizing Ryan O'Donnell's *Analysis of Boolean Functions*.
Upstream source files credit “Asher Yan with Codex” and retain their original
copyright notices. The included revision is
[`164f830312946ccac6e7fdc7bb9493f0149e820d`](https://github.com/Polarnova/FABL/tree/164f830312946ccac6e7fdc7bb9493f0149e820d).

FABL material is distributed under
[Apache License 2.0](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/licenses/FABL.txt).
The TCSlib dataset pipeline extracts, flattens, and repackages the formalizations
and adds generated metadata and prose where applicable. Records preserve upstream
provenance. Inclusion does not imply upstream endorsement. See the
[dataset attribution and license notes](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/README.md#attribution-and-third-party-licenses)
for details. FABL's intermediate metadata is excluded from TCSlib's published blueprint.
Textbook passages and other reference material have separate license conditions.

# How to download it

The dataset is packaged as gzip JSON Lines shards, about %%size\_mb%% MB in total, with a checksum manifest. Each shard contains complete records.

:::::htmlDiv (class := "download-buttons")

::::html a (class := "hero-btn primary") (href := "/tcslib/theorems/tcslib_theorems.manifest.json") (download := "tcslib_theorems.manifest.json")
:::html img (src := "/tcslib/static/arrow.svg") (alt := "") (width := "20") (height := "20")
:::
Download the dataset manifest
::::

::::html a (class := "hero-btn secondary") (href := "https://huggingface.co/datasets/Hydroxyi/TCSlib")
Hugging Face
::::

:::::

Download the manifest and the shards it lists from the deployed site or repository:

* [`dataset/tcslib_theorems.manifest.json`](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/tcslib_theorems.manifest.json)
  in the repository, where every build is a commit;
* [`Hydroxyi/TCSlib`](https://huggingface.co/datasets/Hydroxyi/TCSlib) on Hugging Face,
  for `datasets.load_dataset`.

In Python:

```
import json
from pathlib import Path
from proofmatch.dataset_io import open_dataset

# In a clone containing the manifest and its shards:
with open_dataset(Path("dataset/tcslib_theorems.jsonl")) as f:
    records = [json.loads(line) for line in f]

complete = [r for r in records if r["proof_complete"]]
cited = [r for r in records if r["statement_source"] == "citation"]
with_proof = [r for r in records if r["proof_source"] != "none"]
```

The `proof_complete` flag checks the flattened text for `sorry`. It does not
certify compilation. Use the toolchain and dependency manifest in each record's
provenance when checking its formal statement or proof.

# Columns

* `id`, `lean_name`: the fully qualified Lean name, which is the record key.
* `informal_statement`, `statement_source`, `title`, `definitions`: the statement in prose
  and where it came from; `statement_source` is `citation` or `lean`.
* `informal_proof`, `proof_source`: the proof in prose and where it came from;
  `proof_source` is `citation`, `lean` or `none` (then `informal_proof` is empty).
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
