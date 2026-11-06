# NF's landing (PR #191, a fill gate): resolutions

**Staged (2026-11-05):** `pack.md`, at #191's head `e8994dc1` (the campaign after #190 merged in).
Bundle `95-nf-landing-fill-bundle.md`, SHA-256 `15b5843f3f265051df45e46ad3c020a56adb143de72ae468d4ffed7e4ea1baf8` (415 sections), the records at
`1500583b`; in the exchange `arora-barak-ch3-4/outbox/gates/95-nf-landing-fill-gate/`.

**Replay (2026-11-05): `replay-lnf` passed**, 4 modules, 0 failed, 0 `sorry`; the static check 0
mismatches (`evidence/merged-tree/`). `NTimeHierarchy`'s theorems are on the standard axioms
(`evidence/axioms/NTHAx.out`).

#191 is clear to merge once gate 95 closes with zero blockers and zero majors.

**Dispatched (2026-11-05, the user)**, bundle SHA-256 `15b5843f…`, findings file
`nf-landing-fill-findings.md`.

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/nf-landing-fill-findings.md`,
exchange commit `4da7789c395d2bad6d86d1520d7faf3709d13af9`), SHA-256
`7aa285060b2bd9d5a5c7c6f957f78c00bd7ea5098f9c8a160565650c6a4413f8`.

**Verdict: does not close.** 0 blockers, 1 major (F1, three inline re-derivations of
`BufferWords` identities in `NDNormalForm`), 4 minors (F2–F5), 4 notes (F6–F9). Dispositions
follow below as the repairs land.

**Not yet clear to merge: #191** (gate 95 has a major open).

## Round 1 dispositions (the repair commit `10c015177fde0f9f2b020c010cf44f0f3b3dd37f`)

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Repaired, by the user's ruling (2026-11-05: repair).** The three sites cite `BufferWords`: `nf_bClear`'s `hw` is `rw [h, FinTM.bufferTape_drop R i h0, add_comm]`; `nf_aReturn`'s `hw` and `nf_region`'s cell `\|R\|` cite `FinTM.bufferTape_eq_none_of_not_mem` (in `nf_region` with its side condition `List.length_ofFn`). Statement-preserving body edits (`evidence/round2/freeze/`). The sweep is re-run with the buffer and time-split patterns (finding 5). |
| 2 | minor | **Fixed.** The seal is regenerated on the repaired blob, with candidates taken at its seven imports, so `Build/Contract/Basic`'s definitions (`Turing.Segment` among them) are sealed with controls: 277 candidates (the Lean audit's list = the textual one), both sealed copies 0 diagnostics, all 277 discriminated (272 by generic controls, the 5 derived instances by source controls), 43 of 43 source controls failing sealed (`evidence/round2/seal/`). `NFAx` is re-run on the repaired blob, and the plain elaboration log is shipped (`evidence/round2/axioms/`, `evidence/round2/elab/`). The round-1 pack's rule-10 and axiom lines described `c528e375` plus the seal; that is recorded here as an erratum. |
| 3 | minor | **Fixed.** `nf_pack`'s `hinit` is `(Cfg.mapState_eq_of_fields _ e _ …).symm`, as `nf_tag`. The other eleven `Cfg.ext` blocks are configuration-record equations, not renamings (the auditor's classification, confirmed in the sweep). RN-1's accounting is corrected in the ledger. |
| 4 | minor | **Fixed.** The headline's proof sketch follows the implemented route: the display of `2k + 4`-bit records (choice bit, claimed reads, end flag) on tape `0`, the control sweep, the replay sweeps against two-cell blocks on tape `1`, the constant, the two transfers, the relabeling. "Fill obligations, named: …" is dropped. Docstring only. |
| 5 | minor | **Fixed.** The screen is re-run with `TuringMachine/BufferWords` in the population (`evidence/round2/screen/`): 1,444 declarations, 13 pairs, 5,191 characters at the repaired head; 0 new and 0 gone against both round-1 runs; the one changed pair lost the hand-written buffer indexing the repair removed. The sweep adds `bufferTape_nat`, `List.getElem?_*`, `runFrom_add` and the hand-rolled time splits, with a disposition per hit (`evidence/round2/sweep.md`): the three sites cite `BufferWords`; `nf_pack` cites `CfgFacts`; NF has no RN-1 member left; every other hit is an idiom (the thirteen time-split lines over windows that are not `Segment`-typed; four of the nine sites sit inside one leaf machine, not across a phase redirect, a correction to finding 5's wording). |
| 6 | note | Recorded; no change (history text). |
| 7 | note | Recorded; no change. |
| 8 | note | Recorded; no change. |
| 9 | note | **Recorded in the ledger:** both first-halt sites (`nf_forward`, `ExhaustiveReplay`) in the row candidate; `CodeSimulator`'s private `canonStageBuffer_none` for re-pointing in 12.2c; one numbering for F2 and F8. |

**Replay of the repaired head:** `replay-lnf2` passed, 4 modules, 0 failed, 0 `sorry`, static 0
mismatches, chained from the first cloud snapshot `oleans-cloud0` (`evidence/round2/merged-tree/`),
at #191's head `ac934f99cc5d5009b8027fc0516ab2fd5be0042d` (the repair, then a merge of the campaign
that changes no `.lean` file).

**Round 2 (2026-11-05):** `pack-r2.md`, at #191's head `ac934f99cc5d5009b8027fc0516ab2fd5be0042d`.

**Round 2 staged (2026-11-05)** on the exchange at
`arora-barak-ch3-4/outbox/gates/95-nf-landing-fill-r2-gate/` (exchange commit `1e3a07d8`): bundle
`95-nf-landing-fill-r2-bundle.md`, 84 sections, SHA-256
`cf64d82283e92c74a2a1577ea4aef911664019658a476af2596d0fb4a585b91b`. Lean files from #191's head
`ac934f99cc5d5009b8027fc0516ab2fd5be0042d`, everything else from the records commit
`3db74cec40daa103128d90754940571f47b348a1`. Findings file `nf-landing-fill-r2-findings.md`.

**Not yet clear to merge: #191** (gate 95's round 2 is staged, not yet dispatched).

**Round 2 dispatched (2026-11-05, the user).**

**Replay on the merged tree after #197 (2026-11-05):** `replay-lnf3` passed (4 modules, 0 failed;
modules 4, mismatches 0, static total 0), at #191's head `86cec90d0d46254d1ef3ba01c63f616c970d8072`
(the campaign after #197 merged in; no file of the PR changed), chained from `oleans-lzsa2`
(`evidence/round2/merged-tree-after-197/`). It is the replay of record for the merge while the
campaign's Lean stays at #197's.

## Round 2 findings (received 2026-11-05)

`findings-r2.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/nf-landing-fill-r2-findings.md`,
exchange commit `bacfe4e2636a0d2a1b6f90da8a99d04719e597f1`), SHA-256 `0d59af4db4d8a71e3f35ecf7e24fb938226858740a9eb44c3b9ca25cec7ad6cb`.

**Verdict: does not close.** 0 blockers, 1 major (F1, `nf_split`'s `h0` re-proves
`List.ofFn_getElem`), 2 minors (F2, the sketch's wording; F3, RC-4's use count), 4 notes. Round 1's
major is repaired (notes 4–7).

**Not yet clear to merge: #191** (gate 95's round-2 major is open).

## Round 2 dispositions (#191's commits `dfc3e990` and `49c4d0f7`; head `bbf69680`)

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Repaired, by the round-1 ruling's kind (repair).** `nf_split`'s `h0` is now `(List.ofFn_congr hlen (fun i : Fin s.length => s[i.val])).symm.trans (List.ofFn_getElem s)` (`dfc3e990`). So that round 3 does not find the next one, a library sweep of the whole file followed (`evidence/round3/sweep/`): every `have`, `obtain` and private theorem about core or Mathlib objects only, probed in place by `exact?`, as a generalised `example`, and as its normalised core with `apply?`. It found eight more inline re-proofs, of `Nat.succ_mod_succ_eq_zero_iff`, `Nat.pos_of_mul_pos_left` (2), `Nat.div_lt_of_lt_mul`, `Nat.mul_div_cancel'`, `List.ofFn_eq_nil_iff` and `List.ne_nil_of_length_pos` (2). It also found two chains that are each one lemma, `List.length_take_of_le` (8 sites) and `List.foldl_concat` (7 sites). It flagged an in-file duplicate as well: `nf_prefix_last` and `nf_sweep_record` proved the same prefix-array completion. `49c4d0f7` cites every lemma and makes the duplicate one private, `nf_update_last`. No statement changes; the file is 39 lines shorter. Ledger: the round-2 major's entry records the sweep's results. |
| 2 | minor | **Fixed** (`dfc3e990`, docstring only). The sketch now says that the time is at most `(6W + k(2W + 12)) t + 21 + 15k`, that `t + 1` absorbs the additive terms, and that at `k = 0` the base terms still pay for the guess and the control and input sweeps. The replay sentence says "a work-tape replay". |
| 3 | minor | **Fixed** in the ledger (campaign commit `c1134085`): RC-4 reads "six invocations at five locations" (lines 5203, 6422, 6566, 6778, and twice at 7022), and the 12.2c task re-points all six. |
| 4–7 | notes | Agreed; nothing to do. Round 3 regenerates the evidence note 6 checked: the seal (278 candidates, `Turing.Contract.zero` added by #197), the axioms, the screen and the replay, on the merged tree after #196. |

**Round 3 (2026-11-06):** `pack-r3.md`, at #191's head `bbf696800043c9161f4d233eb26afee32aae8de2`.

**Round 3 staged (2026-11-06)** on the exchange at
`arora-barak-ch3-4/outbox/gates/95-nf-landing-fill-r3-gate/` (exchange commit `664513ff`): bundle
`95-nf-landing-fill-r3-bundle.md`, 96 sections, SHA-256
`f22f8ab68cbc32520e0eb932fdf71878da02109938f4065fbc722afc11f88b08`. Lean files from #191's head
`bbf696800043c9161f4d233eb26afee32aae8de2`, everything else from the records commit
`9b042a84547d0ee46153112fe623599b6cb95a6f`. Findings file `nf-landing-fill-r3-findings.md`.

**Not yet clear to merge: #191** (gate 95's round 3 is staged, not yet dispatched).

**Round 3 dispatched (2026-11-06, the user).**

## Round 3 findings (received 2026-11-06)

`findings-r3.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/nf-landing-fill-r3-findings.md`,
exchange commit `817910c4b99dc56fa38df7bb1c2a0c4a7aaf2b7e`), SHA-256 `c7783917ee4f9ce0bd8aef51888bd3ce115a57bdd75376938f6db638c456a7a3`.

**Verdict: does not close.** 0 blockers, 1 major (F1, `nf_display_firstStop`'s `he` re-proves
`Nat.mul_div_cancel'`), 1 minor (F2, the pack's line count), 5 notes. Round 2's major and the
sweep's repairs are verified (notes 3–7).

## Round 3 dispositions (#191's commit `698dcdf5`; head `b2bac06f`)

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Repaired, by the standing ruling's kind (repair).** `have he := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)` replaces the `Nat.mod_add_div` line and its rewrite, as proposed (`698dcdf5b9d66d05a27b684c4b17ca7f80d97001`). The round-3 sweep missed it because its candidates were typed `have`s and proof blocks, and this `have` is untyped, its content stated only by the rewrite after it. So the sweep is extended by that pattern (`evidence/round4/sweep/`): every untyped `have` or `obtain` whose term heads with a core or Mathlib name, with any rewrite `at` it or `▸` transport within eight lines, and every anonymous `have :=`. Of the eleven library-headed sites, one more is rewritten afterwards: `nf_display_flag`'s `hm` (line 231), the round-3 sweep's C02. No library lemma states it (`exact?` fails on two generalisations; `Nat.mod_eq_sub_iff` leaves a divisibility side goal), so it stays an idiom. The nine anonymous `have`s are `min`/`max` bounds for `omega` and local hypotheses. Ledger: the sweep's entry adds the site and the pattern. |
| 2 | minor | **Erratum** (the dispatched pack is kept): the round-3 change is 3,272 → 3,232 lines, **40 lines shorter**, 39 of them from the sweep (`wc -l` of the blobs; the pack's 3,233 was the linter's count, one more). At round 4 the file is 3,231 lines. |
| 3–7 | notes | Agreed. Round 4 regenerates the seal, the axioms, the screen and the replay on the new head. |
