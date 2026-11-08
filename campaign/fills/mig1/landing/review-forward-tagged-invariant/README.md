# Forwarding tagged-run invariant repoint

**Not yet clear to merge.** The requested third core tagged driver can use the same existing
Mathlib invariant route, without an API/import/controller change. The complete inert candidate
passes both native elaboration and the changed-region strong seal. Actual source is untouched;
the maintainer owns adoption and the final source, screen, census and replay refresh.

`candidate-Primitives.lean.txt` is the complete proposed source, SHA256
`72226a291b0c7e9189883a0ebd75a88ca49bb1f19d0487e54316e542b847ee71`
(419,602 bytes; 7,896 lines). `proposed-repoint.patch` changes only the private
`Turing.FinTM.fwdMapVirtual_run` body and its leading proof sketch. All 311 old declaration names,
full literal headers, visibility, kinds, relative order and 54 public headers are preserved. Every
other declaration chunk, import, attribute, executable/type/data body and every source byte outside
that target's proof/doc block is identical (`freeze.json`). There are no declarations added/removed.
The actual source remains the phase 2 blob `8602e690…`; the completed phase 2 review is immutable.

The new proof's invariant `P u` is exactly the old goal at time `u`: a fresh arrival tag, validity for
the source input head, and equality of the host trajectory with the encoded source configuration.
The existing `fwdMapVirtual_step` and public run equations prove successor preservation. Public
`runFrom_zero` proves the initial tag and configuration; `Set.MapsTo.iterate` propagates it, and
`add_right_iterate` normalizes the clock. No source/host timing, physical input head, component
buffer, emitted prefix, halt behavior or empty-input case changes.

## Actual checks

- Complete inert source plus compiled metadata: **exit 0, zero errors, 15.79 s**.
- Complete inert source with the target guarded before its doc/header: **exit 0, zero errors,
  14.52 s**; 37 foreign ordinary definitions are irreducible and three definition simp attributes
  (`Action.apply`, `Cfg.init`, `MultiTapeTM.initCfg`) are suppressed.
- The actual compiled target is private and non-simp, with no generated descendants under it.
  Its axiom closure contains only `propext`, `Classical.choice`, `Quot.sound`, in both variants.
- Direct compiled inventory finds exactly three foreign ordinary definitions: `VirtualTag`,
  `MultiTapeTM.runFrom`, `MultiTapeTM.step`, all guarded. Four structure-projection abbreviations
  are listed separately. Explicit rewrite/simplifier rule lists contain only public equations or
  local equalities; no foreign or Core/Mathlib definition is supplied as a named unfolding rule.

Both runs used managed wrappers and the complete read-only `oleans-mig1-preflight-current3` tree;
`context.json` pins the toolchain and six direct TCSlib olean artifacts. No olean was written.
All inputs, raw logs and execution receipts are preserved; there were no failed prototype attempts.
Warnings in unchanged full-source regions remain in the raw logs; zero errors is the passing claim.

## Effective control reuse

The previously calibrated 37 pointwise/abstracted control pairs (74 goals) are copied byte-for-byte
with original raw logs, receipts and per-goal coverage under `reused-controls/`. They passed
unsealed and each failed once by `rfl` sealed; the duplicate-first/drop-second adversarial coverage
check rejected the same-total corrupted result. **These controls were not rerun in this prototype.**

`control-reuse.json` verifies all 37 full defining source declarations have unchanged owner, kind,
header/type/data/body code between the prior calibrated context's source and current3. Current3's
new artifacts reflect proof/comment changes; none changes a controlled definition. This includes
all three ordinary definitions reached here. The original controls therefore remain calibrated for
the exact guard scope. No new foreign definition or definition-context change required another run.

## Family and claim boundaries

`family-enumeration/` preserves the preceding read-only inspection. The three unrestricted,
deterministic equal-time core drivers are Simulation's `bufferedSecondCfg_run`, VirtualInput's
`vhostEmitTM_runFrom`, and this forwarding lemma. The first two already use this Mathlib iterator.
The silent and evaluation wrappers already consume canonical run APIs. The narrow ledger scalar
setup-induction exclusion is separate from existential valid-tag propagation.

The all-TCSlib lexical candidate enumeration searched all 22 files containing `VirtualTag` in code,
inspected 16 existential/runFrom theorem-header candidates, and inspected one extra body-induction
candidate. Richer nondeterministic choice-word/liveness and variable-cost macro-time variants remain
separately disclosed; no global tagged-family retirement, exhaustive semantic closure, new debt
approval, or colleague-code repair is claimed.

The 144 phase 2 proof-root names/owner/private flags remain unchanged; line numbers after this
replacement require the parent's actual-source refresh. The parent must adopt, compile the actual
source, refresh the final head screen/census/axiom records and run the required merged-tree replay.
This isolated evidence is not those checks and grants no dispatch or merge clearance.
