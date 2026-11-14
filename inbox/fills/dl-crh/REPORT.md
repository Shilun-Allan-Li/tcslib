# dl-crh — compression checkpoint (route checkpoint 1)

**Status: compression and collision shape proved; `dlHash_crh` is still admitted
on its collision-resistance component. This is not a final completed fill.**

The issue base is `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`; the issued exchange
pack is `b436d19a0310265b214447ea6710deba32df6dd8`. The proof branch is local
`fill/dl-crh` and is never pushed. This is delivery checkpoint 2, following the
initial missing-reader escalation (delivery checkpoint 1).

## User exceptions and scope

The user explicitly authorized adding only `expGenFun_eq` and `expSampleRaw_eq`
in `Candidates/DiscreteLog.lean`, with Rule 10 intact. Both equations are added
with formula docstrings and no simp attributes. All other provider declarations
and bodies are unchanged. This provider already exceeded 1000 lines at the base;
the scoped addition preserves that inherited size issue. All new helpers and the
owned hashing file are below 1000 lines.

The user also overrode host serialization to at most three Lean processes.
This worker checks one module at a time in its own olean tree, counting other
host Lean processes before each launch. The authorized coordination note was
sent to the other fill chats. Exact user wording is in `evidence/authorization.md`.

## Mathematics delivered

- `dlHash_compresses` proves compression from `G.n₀` onward, using valid,
  well-formed generated indices, positive unit residues, domain cardinality
  `2m`, and range cardinality `p - 1 = m`.
- `dlHashEval_collision` proves that distinct domain inputs with equal
  evaluations have different selectors and identifies the discrete logarithm
  with the appropriate modular difference. The selector argument consumes
  published `expF_injective`.
- Generator raw-layout, canonical-key, coin-equivalence, and activation readers
  are proved. Sampler fallback zero and challenge exponent zero are included.
- The reduction machine, polynomial-time postprocessor, typed activation reader,
  and arbitrary-output numeric contract are implemented and checked. The generic
  sampler-to-uniform-residue bound is also checked. Their use in the final
  collision-resistance proof remains in progress.

The target header is byte-identical to the issue base. Its compression component
now applies `dlHash_compresses`; its remaining `sorry` is the original target
admission. No helper contains an admission. The module title drops the statement
phase label, and its results/contents report the actual intermediate status.

## Files and declarations

The complete changed-file list and source commit are in
`evidence/proof-snapshot.json`. `src/` contains all eight changed/new files;
`patches/` contains the entire format-patch series from the issue base.

New declarations comprise the two authorized candidate readers; the hashing
layout/evaluation/range/collision/coin/compression lemmas; and the helper modules
`Encoding`, `Algebra`, `Coins`, `Reduction`, `Probability`, and `Sampling`.
Their exact source, public formula readers, sketches and provenance are delivered.
The generic promotion requests and every conservative private-overlap disclosure
are in `evidence/PROMOTION.md`. No public or private proof was copied. Private
overlaps were rederived through published readers and are explicitly disclosed.

## Checks and raw evidence

- The original pack's seven checksums and 170 source hashes passed. The original
  escalation payload is retained verbatim as `evidence/initial-escalation.zip`.
- Native preflight recorded 12 CPUs, 19,327,352,832 bytes RAM, and
  264,007,364,608 bytes free on APFS. Linux counters are unavailable on macOS;
  the recorded native non-cache headroom proxy is 7,088,668,672 bytes. It is
  explicitly not claimed to be Linux MemAvailable.
- Only the supplied 87 Mathlib roots were fetched. The narrowed cache command
  exited 0, reused 2,339 existing archives, and downloaded none. The cache store
  initially held 32,667 files (1,595,387,830 bytes), origin predating this worker.
  All 11 present packages match manifest URLs/revisions; the four documentation
  packages are absent. No empty olean was found; the Mathlib import probe passed.
- All upstream prerequisites and all eight current changed/new source files have
  successful module checks. The source-hash comparison verifies that the tested
  files are the exact committed bytes. Every check used `lean_check_tree.sh`,
  with timestamps, native Lean maximum resident memory and raw output retained.
  Development failures and their successful repairs are retained, not omitted.
- The checkpoint axiom probe prints only `propext`, `Classical.choice`, and
  `Quot.sound` for compression, collision extraction, canonical generated keys,
  the arbitrary-output postprocessor, sampler switch, and collision probability
  reader. Earlier reduction-machine axiom logs are retained too.
- The full 176-module final order (170 issued modules plus six helpers), final
  sorry-warning comparison, all-stored-constant axiom census, base/final A/B
  seals and paired controls, explicit-unfold scan, and final style-lint comparison
  are **pending final proof completion**. Prepared tools/probes are included;
  no unrun check is represented as a pass.

`evidence/SHA256SUMS` covers every delivered evidence file except itself. Root
`SHA256SUMS` covers the complete payload except itself. The packaging tool checks
exact path-set equality and hashes and verifies that ZIP bytes match the payload.
Only `inbox/fills/dl-crh/` is used for exchange delivery.

Proof commit: `3e12e5e1f5ef6303da3b6c9d55a3c6ac52cd0d8e`. Issue base: `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`.
