# Approved pairDiagTM zero-space fact

**Implemented and bounded checks PASS. Not yet clear to merge.** Only the assigned Encoding
source was edited; parent owns the integrated chain/replay, audit and publication. No source
outside Encoding, Git mutation, commit/push, snapshot/cache write or compiled output occurred.

## Exact source change

Worktree: `/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4`.
Read-only Git checks confirm branch `lean/mig1-followup-api` at
`1160c18f03fd318f0dec25738790935fa61379d4`, with that commit object present.
Source file: `TCSlib/Complexity/TuringMachine/Encoding.lean`.

Immediately after pairDiagTM, the approved theorem is added with a mathematical docstring:

```lean
theorem pairDiagTM_spaceUsed (x : List Bool) (t : ℕ) :
    pairDiagTM.tm.spaceUsed (pairDiagTM.tm.initCfg x) t = 0 := by
  exact MultiTapeTM.spaceUsed_zero_tapes_eq_zero _ _ rfl
```

This is the only new source declaration/proof block. There is no new helper, attribute or
import. Removing the exact added docstring/theorem bytes reconstructs the entire before file.
Thus every prior header/body/definition/table/relative order/import is byte-for-byte frozen.
The before file also matches the frozen API1160 Encoding source exactly.

Before SHA256: `7b67bbcb06ff8acf1c8f6c97b1a468898000747136120dd6420d881115661fe7`.
After SHA256: `e953191d81fde8300e4de1d30ec7e54bb733c32cfa450b44047f1d3a0f36a6b1`.
Exact before/after sources and patch are retained as inert data. The live source matches the
after hash at final verification.

## Actual checks and rule10 boundary

Four sequential plain leanelab checks used the parent-supplied complete read-only mra2 tree,
local3/machine5 slots and authorized scratch lock access. No partial overlay or olean output
was made. Requests/run receipts contain full commands/input/output hashes; Python used -I.

- Full actual owner source plus metadata and actual consumer: exit0/errors0.
- Same full source with the new theorem's complete header/docstring/body in its own scoped
  guard: exit0/errors0. The foreign ordinary definitions spaceUsed/initCfg are irreducible;
  Cfg.init is conservatively sealed too. Default initCfg/Cfg.init simplifier entries are
  disabled. The remainder of the owner file is outside the new section guard.
- A separate actual consumer after that owner source uses the new theorem to establish the
  zero upper bound with pairDiagTM itself, spaceUsed, initCfg and Cfg.init opaque before
  its header. This consumes the actual just-proved theorem, not a hypothetical interface.
- Four definitions have eight fresh point/abstract controls: all8 pass unsealed and all8
  fail sealed under exactly their intended identities. The machine point control reads its
  tape count; the abstract control compares the whole machine. Model controls compare both
  pointwise and complete equations. Both contexts disable the two default init simps.
  Four diagnostic/exit corruptions are rejected by the retained checker.

New theorem and actual consumer have only propext/Classical.choice/Quot.sound. Each has zero
compiled descendants. Recorded direct foreign ordinary definitions are exactly spaceUsed and
initCfg; public FinTM structure projections are abbrev exceptions. pairDiagTM is same-home in
its owner proof: the approved `rfl` discharges only its own zero tape count. It is opaque in
the actual consumer. There are no simp/rw/unfold arguments in either new proof that expand a
foreign definition. Metadata instrumentation is separate from proof source.

The full owner source has **one inherited admission/warning**, pairDiagTM_computes, shifted
from source507 to514 by the insertion. Its raw sorry-token count stays1. The owner native and
sealed runs each report that warning; neither new theorem depends on sorryAx. This evidence
does not claim the entire owner file admission-free or accept the MIG-1 fill.

All4 Lean attempts are retained; no failed proof attempt occurred. The negative controls'
exit1/eight diagnostics are expected tests. `verify.py`, `verification.json`, foreign
inventory, selected snapshot-module hashes and full inputs/logs support these claims. Exact
removal of owner/consumer guard instrumentation reconstructs native source. Selected mra2
input hashes were rechecked unchanged. Full integrated replay and gate remain parent work.
