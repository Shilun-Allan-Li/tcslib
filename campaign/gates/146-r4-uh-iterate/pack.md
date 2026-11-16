# Gate 146 · Closeout R4 UH: Hardness's unary-clock repetition host (PR #335)

**Not yet clear to merge** · PR #335 is a draft, **stacked on PR #334 (gate 145)**: its base
branch is #334's. Seyoon dispatches and merges.

- Lean head: `2dc0fc307ce90b5ae5b56da79b7345c4367183da`.
- Base: #334's head `7bb1f687d87c8faa25c8523fc4bb1e15a5d473c1` (campaign Lean `68cba664` plus R4-1).
- This is the first audit. It can run before gate 145 closes, but #335 merges only after #334.

## Scope

Chapters 3–4 closeout, wave R4, item SG1-UH (`campaign/closeout/REFACTOR-PLAN.md`, R4 row;
`campaign/closeout/r4-design-request/delivery/INTAKE.md`, maintainer addition 3).
- Seyoon ruled on 2026-11-16 to measure this route before deciding.
- The overnight instruction of 2026-11-16 authorizes cleanup and deduplication, to be audited in
  the morning.
- The measurement came out at −295 lines with no new API, so it is proposed here.

The design study recommended carrying UH, because moving the host into a public module would cost
+170 to +370 lines. This PR takes a different route: it deletes the private host and cites an
existing public theorem.

### Changes (`CookLevin/Hardness` only)

- **`clA5Iter_native`** keeps its statement. Its proof now goes through the public
  `Complexity.BinArith.polyTimeComputable_iterate` (`ClassP/BinaryArith/Iterate`):
  - It iterates the counted round `clA5CountStep f` from `pairEncode (1^{N x}) (s x)`, for
    `CN·(|x|+1)^cN ≥ N x` rounds.
  - The counter makes the surplus rounds inert (`clA5CountStep_iterate`: `i` rounds apply `f`
    `min i n` times).
  - The orbit envelope comes from `PolyTimeComputable.output_length_le` on the counter and on `s`,
    together with the supplied quadratic orbit bound.

  New private helpers: `clA5CountStep`, `clA5CountStep_native`, `clA5CountStep_pair`,
  `clA5CountStep_iterate`.
- **`clVisitRows_native`** keeps its statement. Its proof now goes through `clA5Iter_native`
  (`clVisitStep_native`, `clVisitState_size`, `clVisitStep_orbit`).
- **Deleted** (all private):
  - the host: `clRepeatTM`, `clRepeatCfg`, `clRepeat_frame`, `clRepeat_call`, `clRepeat_round`,
    `clRepeat_complete`, `clRepeatWords`, `clRepeat_initial`, `clRepeatOutputTM`,
    `clRepeatOutput_compute`;
  - its ledger and argument packing: `clRepeat_budget`, `clRepeatArgument_native`;
  - the clean-call bridges `clNative_cleanCall` and `clVisitStep_cleanCall`;
  - `clA5_pt_tail`, which was already unused at base.
- **`clA5_pt_eq`** moves, unchanged, above the counted-iteration block so that
  `clA5CountStep_native` can cite it.
- **New import:** `ClassP/BinaryArith/Iterate`. It is cycle-free: Iterate imports only
  `ClassNP/PolyTimeBlockLoop`, which Hardness already imports. It is new to the frozen file and
  needs Seyoon's confirmation.

No public statement changes. Net: **−297 Lean lines** (+130/−427). The deletion also removes five
of the carried item-13 placement layer's 42 use sites.

## Brief for the auditor

1. **Faithfulness.**
   - Check that `clA5Iter_native` and `clVisitRows_native` have exactly their base statements.
   - Check that the counted-iteration argument is sound: the counter is a unary word of length
     `N x`; the round budget `CN·(|x|+1)^cN` bounds `N x`; the orbit bound covers the surplus
     rounds.
   - Check the new docstrings and proof sketches (policy §3).
2. **Deletion.** Check that no remaining declaration mentions a deleted name (all were private).
   Check that nothing else in the item-13 layer becomes dead: `clPlacedAction_eq` was already
   unreferenced at base and is left for the carried item 13.
3. **Rule 10.** Check the evidence (counts below): `seals/`, `controls-part*/`,
   `qa/FOREIGN-ARGUMENTS.json` and `defsweep/`. Review the new proofs' reads:
   - pair projections through `pairFstD_pairEncode`/`pairSndD_pairEncode`;
   - lengths through `length_pairEncode`;
   - iteration through `Function.iterate_succ_apply`.
4. **Copy screen** (population: Hardness): 20 directed pairs gone, none new
   (`evidence/PAIR-DISPOSITIONS.json`). An earlier head (`e73b59f9`) had two new pairs:
   - `clA5CountStep_native` re-derived `clA5_pt_eq`'s citation;
   - `clA5Iter_native`'s ending matched `clA5Le_native`'s.

   Both are fixed in `2dc0fc30` (it cites `clA5_pt_eq` and restates the projection).
5. **Records.** Check that the refactor plan's R4 row, the ledger entry and this pack agree.

## Evidence

- `evidence/REPLAY.json`: the replay of Hardness's downstream closure on #334's replay snapshot
  (`oleans-cl145-c68cb`, the gate 145 output). The driver's stacked mode checks that #334's head
  is an ancestor.
  - 28 modules replayed: 28 passed, 0 failed.
  - 0 inherited admissions in the closure.
- **Seals:** the 5 changed proofs pass with every other-file definition they reach made
  irreducible (7 heads).
- **Controls:** 18 definitions' 36 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 5 roots, 0 explicit reads.
- **Lean-backed sweep:** 28 identifiers, 0 foreign definitions.
- **Lint:** no change.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate146-r4-uh-iterate-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
