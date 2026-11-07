# Forwarding buffer rewind factoring

**Not yet clear to merge.** A routine private proof factoring is viable and tested in inert complete
source copies. The actual Primitives source remains untouched for the maintainer's running replay.

The common lemma `fwdMap_back` has one induction on the active head distance and a Boolean selector
for the active buffer and phase. Its `other : ℤ` argument preserves the inactive work head.
`fwdMap_backB` specializes it to the second buffer with inactive head `|a|-1`;
`fwdMap_backA` specializes it to the first buffer with inactive head zero. Both original headers,
including their exact `j+1` step count, length premise, control phase and endpoint, are retained.
The zero case still takes one blank-reading step when the active word has width zero.

The local same-home `emitterP2_prepare_rewind_bank` provides the same proof pattern for a different
preparation controller. It cannot be called on this forwarding machine. The public `timed_rewind`
interface controls the native input head while leaving work heads fixed; these lemmas instead rewind
one selected work-buffer head, so that published interface does not have the needed contract. The
shared forwarding proof consumes existing `fwdMap_move` and public run, step, tape-block and buffer
read equations. There is no new machine, table, host or public interface, and no admission is filled.
This is a proposed mechanical repair, not an acknowledgment of retained duplication debt.

## Proposed source and freeze

- `candidate-Primitives.lean.txt` is the complete proposed source, SHA256
  `8602e6909919356834430969423a7b9d65b1ebb339cf5529f8a992df8469debe`
  (418,894 bytes; 7,885 lines).
- `proposed-factoring.patch` changes only the two existing private proof bodies and their sketches,
  and adds the private proof lemma and its sketch immediately before the original second-buffer
  lemma. Both old lemmas remain in their original relative order.
- `freeze.json` checks all **310** old declaration headers literally, including **54** public
  headers, visibility, kind and old relative order. Every old definition/inductive/instance chunk,
  every other old proof body, and the imports are byte-identical. The complete source is identical
  outside the exact contiguous proof-family block; the old two headers inside it are also exact.
  Four parser controls include statement-local proof-valued `let` bindings.
- `before-Primitives.lean.txt` is the actual frozen source at SHA256
  `29d84cd418072e50d0a5f5c106daa9eb2dbac5391036684cf6864243afab7db4`.
  It was checked unchanged again after all Lean attempts completed.

## Executed checks

The managed wrapper elaborated the full inert source against the read-only complete
`oleans-mig1-preflight-current2` context. `context.json` records the toolchain and the six direct
TCSlib olean input hashes. No output olean or shared snapshot was written.

| Check | Actual result |
| --- | --- |
| Common-helper prefix | exit 0, zero errors, 7.22 s |
| Complete candidate plus metadata | exit 0, zero errors, 14.45 s |
| Complete candidate with three independently scoped proof-region seals | exit 0, zero errors, 14.54 s |
| 37 paired controls, unsealed | 74 goals pass, zero errors |
| Same controls, sealed | 74 intended `rfl` failures, exactly one diagnostic per goal |

The final strong seal marks **37** foreign ordinary definitions irreducible and removes the three
definition simp attributes (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`) in each changed region.
`seal-v2-manifest.json` verifies that removing only those wrappers restores the exact candidate.
The compiled inventory of all three roots and their three compiler descendants reaches **11**
ordinary foreign definitions, all covered by that guard. Ten additional foreign entries are ordinary
structure-projection abbreviations and are listed separately. The explicit rewrite and simplifier
arguments were inspected independently; only the same-home `fwdMapTM`/`fwdMapCfg` definitions are
named as unfolding rules. Core/Mathlib arguments are equations or simplifier theorems.

All three roots are compiled private, non-simp and not registered for unfolding. All six root and
compiler-descendant axiom closures contain only `propext`, `Classical.choice`, `Quot.sound`, both
natively and in the successful sealed copy. `compiled-inventory.json` retains every direct foreign
definition entry and the complete axiom inventory.

The 37 existing pointwise/abstracted control templates were reused verbatim and **freshly executed**
in this complete context. `control-coverage.json` verifies each actual diagnostic, not just the total;
a synthetic duplicate-first/drop-second result with the same total is rejected.

## Preserved failure and limits

`Candidate-sealed-v1` failed with three instrumentation parse errors because its scopes were inserted
between docstrings and declarations. This is preserved with its input, raw log and receipt. Version 2
moves each docstring inside its section; the candidate proof text did not change. No seal success is
claimed from version 1. Warnings remain in the raw complete-source logs; passing checks mean zero
errors, not zero warnings.

These checks establish the bounded inert candidate. They are not an actual-source compile, merged
tree/downstream replay, before/after whole-module compiled census, screen, external gate closure,
or merge clearance. No actual Lean source, Git state, cache or shared snapshot was modified; there
was no commit, push or dispatch. The maintainer owns adoption after the current replay and the
subsequent source/evidence refresh.
