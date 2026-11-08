# Existing NONE-first-halt inline candidate

This is an additional observation, excluded from the six-change proposal and all probe/pass
counts. No source edit, whole-file check, broader duplication clearance or debt disposition
is made here.

In exact b1 Loop.lean:3005–3040, emCall_eval_first locally takes Nat.find of the existence of
a halted source run, proves its first cut, then gets output with computation output_unique.
The already-existing public MultiTapeTM.exists_first_halt has the exact source-run premise:

- Let hspec = (computesInTime_iff M s out T).mp hM.
- Apply exists_first_halt M.tm (M.tm.initCfg s) hspec.1.
- Its returned t≤T and earlier ¬Halted cut have the existing hlive type, via the published
  Halted abbreviation; its COMPLETE configuration equality to time T transports both
  hspec.1 (halt) and hspec.2 (arbitrary output) to time t.
- The existing virtual-tag/lockstep/cut proof after that extraction is then unchanged.

This would replace the local least-time and output-uniqueness subproof without a new public
API/import or live-stop transformation. It is distinct from the three assigned live-stop
private forwarding headers. That operational body also mentions private MIG evaluation
interfaces, so it was not silently included in the stable-preflight generic-header probes.
Root may commission/check the actual inline repoint separately after source is allowed to
change. This note does not expand the current six mandatory transformations or authorize a
source edit before the prerequisite gate/merge.
