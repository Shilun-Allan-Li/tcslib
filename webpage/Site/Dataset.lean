import VersoBlog

open Verso Genre
open Blog hiding lean
open Site

#doc (Page) "Dataset" =>

::::htmlDiv (class := "page-title")

The theorem dataset

A mixed and growing set of theorems of theoretical computer science formalized in
Lean 4, one record per theorem of the library, with the informal statement, the formal
statement, the proof, and where the mathematics came from.

::::

# What it is

Every theorem and lemma of TCSlib that has a blueprint entry is one record. A record pairs:

* an informal statement in prose, with the definitions it relies on;
* a standalone formal statement: a Lean 4 file that ends with the declaration, its proof
  replaced by `sorry`, carrying the definitions, instances and context the statement needs;
* the proof: a second Lean 4 file with the declaration proved for real and its whole
  dependency closure within the library flattened into it, so it compiles with Mathlib alone;
* a difficulty rating of the Lean proof script, from 1 to 7;
* provenance: a citation into the passage of the paper or textbook chapter the result was
  formalized from, or, when no such text was attached, an account written from the Lean proof.

The set is **mixed**, and the records say how:

* **Some proofs are still open.** When the proof, or the proof of something it depends on,
  still contains `sorry`, the record's `proof_complete` is false. At the October 2026 build
  that is 61 of 4,179 records.
* **Not every record cites a text.** 361 records cite a source document: either the passage
  that proves the result (`proof_citation`) or one that states it while the Lean proof differs
  (`statement_citation`). 496 carry only an informalized account of their Lean proof, because
  the text they were formalized from was never attached. The remaining 3,322 have no proof
  note yet.
* **Informal statements have two origins.** `statement_source` is `blueprint` when the prose
  is the blueprint author's own and `regenerated` when it was written from the formal
  statement by a language model and checked against a rubric.

The set is **growing**: it is rebuilt incrementally from the library, so each build adds the
newly formalized declarations and the counts above change. The
[theorem viewer](/tcslib/theorems/) shows the live numbers of the build that is deployed,
lets you filter by provenance, and draws the dependency graph of every statement and proof.
By area at the October 2026 build: Boolean function analysis 1,602, complexity theory 1,433,
communication complexity 726, learning theory 211, error-correcting codes 147, graph theory
40, locally decodable codes 16, cryptography 4.

# How to download it

The dataset is one gzipped JSON Lines file, about 30 MB, one JSON object per line:

* [`tcslib_theorems.jsonl.gz`](/tcslib/theorems/tcslib_theorems.jsonl.gz) from this site, the
  build that is deployed;
* [`dataset/tcslib_theorems.jsonl.gz`](https://github.com/Shilun-Allan-Li/tcslib/blob/main/dataset/tcslib_theorems.jsonl.gz)
  in the repository, where every build is a commit.

In Python:

```
import gzip, json

with gzip.open("tcslib_theorems.jsonl.gz", "rt") as f:
    records = [json.loads(line) for line in f]

complete = [r for r in records if r["proof_complete"]]
cited = [r for r in records
         if r["proof_notes"] and "citation" in r["proof_notes"]["kind"]]
```

The `proof` column of a complete record compiles in a project that depends on the same
Mathlib version as the library (`lake-manifest.json` in the repository pins it). The
`formal_statement` column reproduces the declaration's environment as faithfully as a
flattener can; the builder measures the compile rate of a sample on every run.

# The record

* `id`, `lean_name`: the fully qualified Lean name, which is the record key.
* `title`, `statement_informal`, `definitions`, `informal_statement`, `statement_source`:
  the informal half.
* `formal_statement`, `upstream_defs`, `n_upstream_defs`: the formal statement and the
  definitions it carries.
* `source_module`, `kind`: the Lean module; `theorem` or `lemma`.
* `difficulty`: integer 1 to 7, or null when unrated.
* `proof_sources`, `proof_steps`, `proof_notes`: provenance; `proof_notes.kind` is
  `proof_citation`, `statement_citation`, `informalized`, or a citation `+informalized`.
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
