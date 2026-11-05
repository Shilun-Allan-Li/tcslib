# Gate 97 (G5's consumer API, #197): resolutions

**Staged (2026-11-05)** on the exchange at `arora-barak-ch3-4/outbox/gates/97-zone-step-api-gate/`
(exchange commit `421de225`): bundle `97-zone-step-api-bundle.md`, 91 sections, SHA-256
`e1de882fd8ddb022d276e61fbc74ab3a3fcb5dc5a2be884dc48abe9a8e3c84b8`. Lean files from the PR head
`0a1b64d59b707df679e66201496f2bced7197a98`, everything else from the records commit
`6ab5d4c8f6e8472abd52ad8c278f447b7a1c359a`. Findings file `zone-step-api-findings.md`.

**Replay (2026-11-05): `replay-lzsa` passed**, 111 modules, 0 failed; the static check 0
mismatches, the campaign's existing 45 `sorry`s (`evidence/merged-tree/`).

#197 is clear to merge once gate 97 closes with zero blockers and zero majors.

**Supplementary sweep before dispatch (2026-11-05, cloud session):** the inline-step sweep and the
statement-shape grep that gates 95 and 96 found missing (their F5 and F6), run on #197's added
lines: no hit, and one candidate, the private `zs_rowPre_mapState`, which is RN-1's kind (at most
an accounting minor) (`evidence/sweep/README.md`). The staged bundle stands.

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/zone-step-api-findings.md`,
exchange commit `60bbdc84187f9a910222845eab2e8fd3f304426d`), SHA-256
`a4b9f7a53941f34b1cbb8f2080b5189ae2a7073ebd69c2a42f2f1e1d15336eac`.

**Verdict: PASS.** 0 blockers, 0 majors, 6 minors (F1–F6), 7 notes (F7–F13). The gate closes
with the minors swept in a closing commit on #197, F1 re-verified by a sealed elaboration of
`ZoneRebalance` with `Contract.zero` irreducible, and the merged-tree replay re-run. Dispositions
follow with the sweep.

**Not yet clear to merge: #197** (the closing sweep and its replay are owed).

## Round 1 dispositions (the closing commit `20e7fc756c8298ba043913eb60657fde84472c5d`)

The gate passed (0 blockers, 0 majors). The six minors are swept in one closing commit on #197,
`20e7fc756c8298ba043913eb60657fde84472c5d`, on top of the audited head
`0a1b64d59b707df679e66201496f2bced7197a98`.

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Fixed.** `zr_anchorContract` is a `def` again, and `zr_pinAnchor_step` is proved by `zr_pinRe_step` with `Contract.zero`'s published `zero_post`, `zero_time`, `zero_lo` and `zero_hi`, the auditor's construction. Re-verified by a sealed elaboration of `ZoneRebalance` with `Turing.Contract.zero` (and 21 further definitions in each changed stretch's own section, 22 in all (`seal-set-zr.txt`)) irreducible, with its `rfl` and equation controls (`evidence/rule10/closing/`): the sealed copy of the whole file elaborates with **0 diagnostics** (461 s); the controls pass 49 of 49 unsealed and fail 49 of 49 sealed. `ZoneStep`'s own seal, re-run on the closing commit, elaborates with 0 diagnostics. |
| 2 | minor | **Fixed.** The last step of `sum_cost_le_of_count` is `simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. The pack's attestation ("every `simp` call is `simp only`") was wrong at the audited head; it holds at `20e7fc756c8298ba043913eb60657fde84472c5d`. |
| 3 | minor | **Fixed.** `zoneRowPre_iff` and `zoneRebalanceIndex_eq` state their formulas. |
| 4 | minor | **Fixed.** The facade's `Build/ZoneStep` entry cites `[AB09, §1.7]`. |
| 5 | minor | **Fixed, by the user's ruling (2026-11-05: publish).** `zoneRowPre_congr` (two configurations over any state types with equal work tapes and equal head `0` satisfy `zoneRowPre D` together) and its corollary `zoneRowPre_mapState_iff` sit beside `zoneRowPre`; `ZoneStep` cites them, and its private `zs_rowPre_mapState` is gone. Both names are unused on all 199 refs searched (the campaign, `main`, every PR head). `ZoneRebalance`'s twelve inline re-derivations are recorded for the 12.2c window (`duplication-ledger.md`). |
| 6 | minor | **Fixed.** The statement-shape search over every ref (339 branch heads) is `evidence/names/shape-search.md`; the inline-step sweep is `evidence/sweep/README.md`. No copy found. |
| 7 | note | **No change.** A G5 round that composes track steps gets a positive time from its own seams: `Contract.seq_positive`, `Contract.branch_positive` and `Contract.inPhase_positive` hold unconditionally, so exporting `some entry ∉ X` is not needed for the loop host. |
| 8 | note | Recorded; no change. |
| 9 | note | Recorded; no change. |
| 10 | note | **Fixed.** The section comment above the equations now names what it covers and says that `zoneRowLo` and `zoneRowHi` have no equations yet. |
| 11 | note | **No change.** The hand-written `Contract.zero_*` equations stand; `simps!` would give the same lemmas. |
| 12 | note | **No change.** The names `sum_two_pow_le_of_count` and `sum_cost_le_of_count` are kept: G5's plan cites them, and their statements are general arithmetic, not zone-specific. |
| 13 | note | **Errata recorded.** The restricted `ZoneStep` screen ran at `e110d886`; the changed-files screen at `0a1b64d5` covers it. The axiom probe is extended to every new public constant at `20e7fc756c8298ba043913eb60657fde84472c5d` (`evidence/axioms/closing/`): all 31 new public constants (`Contract.zero` and its five equations, the fourteen `simps` field equations, the five declared equations and the six `ZoneStep` constants), and the 27 prefix-sweep lines, on subsets of `[propext, Classical.choice, Quot.sound]`; no `sorryAx`. |

**Replay of the closing commit:** `replay-lzsa2` passed, 111 modules, 0 failed, static 0 mismatches,
the campaign's existing 45 `sorry`s, chained from the first cloud snapshot `oleans-cloud0`
(`evidence/closing/merged-tree/`), at #197's head `fde50a5a72c7dfa34699a2968255a67dec1965ef` (the
closing commit, then a merge of the campaign that changes no `.lean` file). One correction during
the sweep: minor 2's first list named `smul_eq_mul`, which the chain check rejected (the scalar is
`ℕ`'s `nsmul`); the commit was amended to `nsmul_eq_mul` and `Nat.cast_id` before it was pushed
(`evidence/closing/chain/log.txt`).

**Gate 97: CLOSE (2026-11-05).** Round 1 passed with 0 blockers and 0 majors; the six minors are
swept in the closing commit and re-verified (minor 1 by the sealed elaboration of
`ZoneRebalance`), and the merged-tree replay of the closing commit passed. #197's base is the
campaign branch.

**Clear to merge: #197** at `fde50a5a72c7dfa34699a2968255a67dec1965ef` (gate 97 closed;
`replay-lzsa2` passed).

**Merged (2026-11-05, the user):** #197 at `33ceeed161301fa5147826c25d40265e3d7528a5`. The campaign's
Lean tree is now #197's head `fde50a5a`'s, so `replay-lzsa2`'s snapshot `oleans-lzsa2` is the
campaign's snapshot and the replay of record.
