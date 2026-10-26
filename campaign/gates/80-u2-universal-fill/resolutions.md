# U2, the `k`-tape universal machines (PR #168, a fill gate): resolutions (round 1 FAIL; round 2 PASS; gate CLOSED)

**Gate:** the fill gate of PR #168 (`lean/u2-universal-landing` at `fd995ec1`). Pack `pack.md`;
bundle SHA-256 `7de06b274ad75beee61c39b27bb70f6845d95648260b53fc911440d52d75b0b5` (164 sections),
the records at `a1c9ec5d`. **Round 1: FAIL, 0 blockers, 1 major, 1 minor, 10 notes**
(`findings.md`, verbatim).

**The user's rulings (2026-10-26):**
- finding 1: keep D1, and answer it with the campaign's convention on reducible abbreviations,
  now written into the standards;
- finding 2: fix the sketch on #168.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | D1 (`uk_loop_forward` citing `MultiTapeTM.exists_first_halt`) reads its prefix `∀ v < t₀, ¬ (…).Halted` as `state ≠ none`, a definitional use of the TCSlib predicate `Cfg.Halted`; the landing seal omits it; the coverage misses three new citations. | **Answered by the convention (user, 2026-10-26); the coverage added.** <br>• **What `Cfg.Halted` is:** `abbrev Cfg.Halted cfg : Prop := cfg.state = none` (`TuringMachine/Configuration.lean:226`), reducible, with no `_iff` lemma. <br>• **Lean cannot seal it.** `HaltedSealProbe.lean.txt` (`evidence/round1/`) tries `attribute [local irreducible] Turing.Cfg.Halted` and gets "failed to set `[local irreducible]`, `Cfg.Halted` is currently `[reducible]`, `[semireducible]` expected". The two-step route via `[local semireducible]` is refused the same way. So the proposed fix (add it to the seal, with a control) cannot be built. <br>• **The convention predates this gate.** The C1 core briefs allow the reading: "reading `¬ Cfg.Halted c` as `c.state ≠ none` is allowed" (`campaign/fills/c1/briefs/c1-fill-core-cont1.md:239`, `-cont2.md:284`). Gate 34's review records abbreviations as unsealable, their definitional uses "by design" (`campaign/gates/34-brief-api/evidence/r3/gate-review-r2.md:119`). <br>• **The library consumes published `¬ Halted` hypotheses this way** throughout: `Build/Catalog`'s `hlive`, `ClassNP/EXP`, `ClassNP/SAT`, `CookLevin/Hardness`. <br>• **Now in the standards:** `policy.md` (*Definitions land with their lemmas*: reducible abbreviations are notation) and `campaign/standards/TEMPLATE.md` (seals and reducible abbreviations). <br>• **D1 stays.** It removes a re-derivation of a published lemma (the review's F1a); it adds no unfolding of a sealable definition. <br>• **The coverage:** the worker's import probe, extended by `MultiTapeTM.visitedByTapeHead_mono`, `FinTM.ComputesInTime.spaceUsed_le_of_halt` and `Cfg.Halted` (`exists_first_halt` was already listed), gives **597 checks of 596 names, 0 errors**, against the tree after #164 (`evidence/round1/LandingImportProbe.*`; the two deprecation warnings are the worker probe's own). <br>• **Backlog:** publish `Cfg.halted_iff` with the next API PR that touches `Configuration` (its closure is most of the library, so not alone). |
| 2 | minor | `exists_selfUniversalK`'s sketch writes `T_α + D·t`; the proof's ledger is `T + 1 + v`, `v ≤ D·t`. | **Fixed** by `948df2f9` on #168, docstring only: the lockstep runs through the first halt `t₀ ≤ t`, and the time is `T_α + 1 + D·t`. The code is identical with comments stripped. The new head elaborates against `oleans-la1m` with both targets on the standard three axioms (`evidence/round1/UniversalK-948df2f9-ax.out`). |
| 3–12 | notes | Integrity and scope; the machine and configuration definitions; F2's ruler layout; U2-U's constants and ledger; U2-E's constant and Implementation paragraph; the converses and boundary cases; the duplication screens; rule 11 and the evidence; F5 and F9; the pending replay. | No action. Note 12's replay is #168's merge condition: the 3-module closure chained from the snapshot #167's replay leaves. |

**Round 2** audits the answer to finding 1 and the fix of finding 2 (`pack-r2.md`).

## Round 2: PASS, 0 blockers, 0 majors, 2 minors, 6 notes; gate CLOSED

Pack `pack-r2.md`; bundle SHA-256 `fe5f0f8ad8bd2b5acceed600d774c645f266eccc2fd73878cdcb6df0b62cc764`
(29 sections), the Lean at `948df2f9`, the records at `7a1370d7` (`findings-r2.md`, verbatim).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The extended probe covers the proof-term walk, not every source-level tactic argument: 17 external theorem names cited in the source have no check. | **Fixed.** The 17 (`Fin.coe_castAdd`, `Fin.coe_castLE`, `Fin.coe_castLEEmb`, `Fin.coe_castSucc`, `Fin.coe_natAdd`, `Fin.val_last`, `List.cons_append`, `List.getElem_cons_succ`, `List.getElem_cons_zero`, `List.length_cons`, `List.length_nil`, `MultiTapeTM.initCfg_with_q₀`, `Nat.add_zero`, `Nat.mul_zero`, `SignType.coe_one`, `SignType.pos_eq_one`, `true_and`) are added, found as the external `thm` rows of the review's `out/20b-tactic-arg-kinds.out` absent from the probe (`evidence/round2/tactic-args-not-in-probe.txt`). **614 checks of 613 names, 0 errors**, against `oleans-lriseqm` (`evidence/round2/LandingImportProbe2.*`). The remaining rows are the core simproc `reduceIte` and the module's own privates. |
| 2 | minor | "Lean cannot seal an abbreviation" is stronger than shown: the error names the override `set_option allowUnsafeReducibility true`. | **Fixed in the standards.** `policy.md` and `TEMPLATE.md` now say the standard seal cannot cover it: Lean's default reducibility validation refuses the attribute, and the unsafe override is not used in seals. The convention, which round 2 accepts, does not depend on the stronger claim. |
| 3–8 | notes | Integrity and the documentation-only delta; the convention resolves round 1's major; the sketch fix; the axioms; no reopened point; the pending replay. | No action. Note 8's replay is #168's merge condition. |

**Merge state. #168: not yet clear to merge.** The gate is closed. Its 3-module merged-tree replay
(`UniversalK`, `SelfUniversal`, the `TuringMachine` facade) runs once #167 has merged, chained from
`oleans-lriseqm` (or from #166's snapshot if #166 merges first). #168 then merges the campaign.
**#166 merged (2026-10-26, `26ae1f10`).** The campaign is merged into #168 (head
`3117770f2ff36150dc489f2f0c1c30bca0e3a0f0`; its three files keep the gated blobs).
`replay-lu2m` (`campaign/fills/u2s/evidence/u2s-universal-landing/merged-tree/`), 3 modules
chained from `oleans-lscpm`, is written; its precheck passed.
