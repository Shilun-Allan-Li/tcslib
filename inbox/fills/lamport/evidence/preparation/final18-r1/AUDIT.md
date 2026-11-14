# Frozen candidate 252ec: final eighteen inventory preparation

All eighteen one-target inventory phases were prepared from commit
`252ec646b9a5605c11aa245629a4ce8f404f74e8`. **No Lean check was run by this preparation.**
The queue is `queue.json`; each record names the root/evidence paths, target, unique phase,
immutable source hashes, inventory order, planned collector attempt/log path, and closure.
It requires completion of the root's final canonical-product sweep before native checks.

The preparation used the exact copied tool at `tools/prepare_seals.py`, whose SHA-256 is
recorded in `plan.json` and `queue.json`. The orchestrator is copied beside it. Raw
preparation logs and `results.jsonl` are under `evidence/logs/final18-preparation-r1/`.
Earlier Base, BaseAuth, and checkpoint inventory/seal attempts were not replaced or rerun.

## Scope, source, and root census

The candidate changes the owned module, the authentication registration facade, and sixteen
new helpers. `sources/` preserves all eighteen exact Git blobs. Each current source matched
the frozen blob and the root's 177-module final-order source audit during preparation.

`helper-source-audit.json` records all sixteen helper headers, immediate public docstrings,
declaration lists, hashes, and line counts. All required fields were present. Every helper
is below 1000 lines (64–452 lines); the owned module is 973 lines. New definitions publish
their previously reviewed equations/field readers. Native axioms and Rule-10 checks remain
separate evidence.

`mathlib-root-audit.json` recomputes the direct Mathlib imports of all 177 final-sweep modules
from frozen Git blobs. The set is exactly the issued **82 roots**; no root was added.

## New helpers absent at issue base

Every one of the sixteen new helper paths is **ABSENT** at issue base
`eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`. The JSON records each status and nonzero Git
exit; `issue-base-helper-absence.log` retains the actual `git cat-file -e` commands/errors.
There are no empty-source or fake base compilation phases for these files.

## Duplication review finding requiring follow-up

The final ledger search found exact **public** versions of the two generic variable-prefix
FP wrappers:

- `TCSlib.Cryptography.takeLen_poly`, `Asymptotic/ReductionSupport.lean:248`;
- `TCSlib.Cryptography.dropLen_poly`, `Asymptotic/ReductionSupport.lean:256`.

`ReductionSupport` is already module 105 of the issued and final sweep, with no additional
prerequisite module or Mathlib root. Candidate 252ec still independently derives these as
`LamportMachine.take_poly/drop_poly`. The binding duplication rule requires importing and
using the public versions. The coordinator was notified immediately; **no frozen source was
edited by this preparation**. A reviewable candidate is in `drafts/Machine-public-reuse.lean`:
it imports ReductionSupport, removes the two duplicate wrapper declarations, and replaces
their internal calls with the public names. A source fix requires fresh native/snapshot
evidence for the new final revision; the eighteen prepared 252ec phases remain historical
evidence for exactly the candidate they name.

The same result also has private occurrences `Candidates/DiscreteLogHardcore.lean
dlb_take_poly` and `dlb_drop_poly` (1082/1088), besides the previously recorded
`ClassNP/TMSAT.lean tmsat_pt_take` and `CookLevin/Hardness.lean clA5Drop_native`. Those private
proofs were not copied. Removing the redundant wrappers eliminates these overlap items from
the final delivered Machine helper rather than accepting more duplication debt.

Retain the checkpoint-1 overlap record:

**overlap: TCSlib/Cryptography/Asymptotic/OneWay.lean ofFn_blocks_two_symm**.

The table serialization argument rederives the two-block identity from published
`FunFamily.ofFn_blocks_symm` and `OneWay.flatten_ofFn_two`; it does not copy the private proof.

Retain the independently derived serialization overlap:

**overlap: TCSlib/Cryptography/Authentication/Signatures/Lamport.lean lamportVerFun_sign.hflat**.

`MachineSpec.publicWord_flatten` reads the same serialization identity from public encoding
and list equations. There is no public reader for the old local `hflat`; the general helper
is a promotion candidate.

## Promotion ledger refresh

- Encoding injectivity and equality readers belong with the shared cryptographic encoding.
- The cost-zero return lemma is generic OracleComp support, consumed by the one-query proofs.
- Table/seed serialization is construction-specific, with general word/cast/block facts
  promoted when another consumer needs them.
- Favorable-pair counts, optional-query averaging, finite maximum selection, and the generic
  coordinate-reduction bound are shared probability candidates.
- The owned generic codec-extensionality reader belongs with MachineCodec support.
- `Blocks.flatten_ofFn_update`, `MachineSpec.publicWord_flatten`, and `headD_drop_ofFn`
  are general list/encoding readers.
- Binary index encoding, its width/value readers, and the bounded decoding/advice wrapper
  are generic reduction support candidates.
- The Closing polynomial-loss and signature-reduction closure lemmas are generic asymptotic
  or signature-interface candidates.
- The nonabort-safety implication is presently stated for the typed Lamport oracle; a
  generalized one-query interface can be promoted on demand.
- No new expectation/`uexp` bridge was copied: InversionProbability imports the existing
  public `Games.Bridges.Experiments` laws.
- The generic `take/drop` FP wrappers are **not** promotion requests once the already-public
  ReductionSupport APIs are reused.

## Subsequent verification

Run each phase's snapshot then Inventory, one module per checker call, only after the root
releases its compiler slot. The planned collector raw path is in the queue. Then run the
preserved preparation tool's `prepare` against that raw collector log, execute each A/B seal
and control through `run_seals.py`, and run its explicit-unfold scan. The inventory itself
prints axioms for every stored constant in the snapshot; preserve the complete raw census.
For a helper with no TCSlib import closure (Blocks), zero requested TCSlib seals are a valid
empty closure, not a simulated negative control. Main/Auth supply paired full-closure
sensitivity controls; each actually generated sealed negative must fail exactly once.
