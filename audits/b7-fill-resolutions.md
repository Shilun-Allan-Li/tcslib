# B7 fill gate (deterministic logspace, 12 targets): resolutions (CLOSED, round 1)

## Round 1 (2026-10-12): 0 blockers, 0 majors, 1 minor, 23 notes

The findings are verbatim in `audits/b7-fill-findings.md`. The pack is `audits/b7-fill-pack.md`,
with its 89-file bundle `audits/b7-fill-bundle.md`. The auditor found all twelve targets proved
as the routes prescribe. It confirmed:
- the cumulative freeze, by reconstructing every head file from the patch: twelve replaced
  bodies, the nine advertised publics, and imports unchanged (note 2);
- the oracle-input simulator's frame, oracle and space contracts, with no monotonicity
  inserted on `sb` (note 3);
- N1's streamed validation, which never accumulates the query's value (note 5);
- N3's outer-only canonicality (note 6);
- N4's width-before-decode and twice-cap storage bound, with the inner field never decoded
  (note 7);
- the multiplication invariant **proved**, discharging T11 and Q8 (note 9).

It ruled each of the nine exports correctly stated and genuinely shared (notes 10–18). It
ruled **the 55% cross-batch pair to be idiom**, shared application of the public
`pairEncode_getD`, needing no debt acknowledgement (note 19). It reran both screens exactly:
192/53 → 416/79 (note 20). It confirmed that the two parallel batches are disjoint and compose
(note 21). It also checked the machine by direct transcription: `multARM` against the
language on all 4,095 words of length at most 11, plus the composition preimage identity
(131,040 checks) and the capped searches.

| Finding | Disposition |
|---|---|
| 1 (minor): the pack's named comparison of the multiplication arithmetic against `Machines/Bin.lean` is not reproducible, since `Bin.lean` was neither attached nor in the screen population | **Resolved, evidence only; no source change.** The maintainer ran the comparison at the campaign tip (`audits/logs/b7-fill-close-bin-screen.log`). In the two-file screen of `Logspace/Mult.lean` and `Machines/Bin.lean` (60 declarations, 4 pairs), **no pair joins the two files**. Three pairs are Mult's known in-file pairs (`multRow_cons` ↔ `multRows_cons` 80–81%, `mult_outer_loop` → `mult_inner_loop` 54%), and one is internal to `Bin`. With `Bin.lean` added to the 22-file population (422 declarations, 83 pairs), the four new pairs all involve `Bin.lean` and none involves a B7 file. The multiplication arithmetic therefore copies nothing from `Bin`. The bundle-building checklist now requires every file a pack names in a check or hazard list |
| 2–24 (notes) | Confirmed. Note 24: replay, axiom and lint execution, and the delivery shims' non-execution, remain integration-side attestations, as the pack states |

**A pre-existing pair surfaced by the comparison, outside this gate.** Adding `Bin.lean` to the
population shows `Bin.lean::bits_getLast` reproducing `FragDec.lean::bits_head_odd` at 260/288
(90%), and `Bin.lean::bitsVal_bits` at 74%/54% in the two directions. Both files are received
material (Hydroxyi, `f70c57c2`, audited at P0), and neither changed in the campaign. The two
lemmas prove different facts about `Nat.bits`, the last bit and the head bit, by the same
strong-induction idiom. No B7 delivery touched either file. This is recorded for the colleague
sync on the received program layer (`backlog.md` §2), not as campaign debt.

**Gate CLOSED.** The twelve B7 targets, from the oracle-input simulator through
`multLang_mem_LOGSPACE` ([AB09, §4.3, Example 4.7, Lemma 4.17]), are filled, admission-free and
audited, with the nine exports confirmed. Cluster B7 is complete.
