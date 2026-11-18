# io-phfe: dispatch pack (degree-2 PHFE from DLIN, [Wee20] in the JLS26 pipeline)

The second iO-components job (IOComponentsPlan.md): one end-to-end Codex job in a local checkout,
**Phase A** (explicit functions, correctness, security inequalities; efficiency written, not proved),
with a statements gate on its checkpoint 0 and a proofs gate on its final. Static only; nothing is
committed or dispatched.

- **r1** was prepared 2026-11-18 at records `0fec2589`, blocked on sources.
- **r2** was prepared 2026-11-18 at records `1a9a3295`, from the staged PDFs and the rulings of
  2026-11-18 (journal pipeline, generic FE, Q-S2 fixed prime, p as an input, subexponential
  security #374, two phases, uniformity, sampling).

## Contents

| File | What |
|---|---|
| `sources-r2.md` | **r2.** The three PDFs with SHA-256 and revisions; every location used, with pages; **the pinned chain**: JLS26 Thm 5.1 → GJLS21 Thms 10.3/10.4 → the §9 PHFE ingredient = **[GJLS21, Definition 4.3]** (ε = 1, many-key) for F^PHFE, with Defs 4.1, 4.2, 4.6; the gap table G1–G8 between Wee20 and that notion; Wee20's misprints |
| `design-r2.md` | **r2.** Rulings applied (§ 0); target and bridges (§ 1); Phase A deliverable (§ 2); layout (§ 3); statement shapes: DLIN, MDDH self-reduction, reduction functions and realisers, generic FE in Def 4.3 form, classes, partial garbling, Π, quadratic scheme, `wee20PHFE`, headlines, efficiency `Prop`s (§ 4); proof plan (§ 5); milestones and size ~7.4–13.8k (§ 6); **questions Q1–Q5** and the r1 questions settled (§ 7); risks; extensions |
| `duplication-sweep-r2.md` | **r2.** r1's table with lines re-checked, plus `Foundations/Subexponential` (must-reuse), NUPPT activation, uniformity and time-bound items, Mathlib rows for MDDH and partial garbling, false friends, and in-house items expected at `<BASE>` |
| `dispatch-prompt-r2.md` | **r2.** The prompt Seyoon pastes into Codex (Phase A only), with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>` only. It cites [GJLS21, Definition 4.3] and Wee20's §3 claim, §3.3, Theorem 1 and Lemma 1 |
| `sources.md`, `design-r1.md`, `duplication-sweep.md`, `dispatch-prompt.md` | r1, kept for the record; superseded by the r2 files |

## The chain (sources-r2 § 3)

- [JLS26, Thm 5.1, p. 21] = [GJLS21, Thms 10.3, 10.4, pp. 63–64]. These are GJLS21's iO theorems with
  Wee's PHFE in place of GJLS21 Thm 8.1, consuming the PHFE ingredient of [GJLS21, §9, pp. 57–58].
- **That ingredient:**
  - public-key; syntax Def 4.1;
  - correctness Def 4.2, the value in G_T;
  - **1-simulation security for unbounded keys: Def 4.3 at ε = 1 (Remark 4.3), many-key
    (Remark 4.6)**. The adversary commits to (x*, y*) and all keys before pp; one ciphertext; a
    universal stateful simulator;
  - linear efficiency, Def 4.6;
  - the class (x, y) ↦ [Σ_{j,k} f_{j,k}(x) y_j y_k]_T with constant-degree f_{j,k}; one prime p per λ.
- **[Wee20]**: no numbered theorem for its main scheme.
  - The claim is in §3, p. 6, proved in §3.3: semi-adaptive simulation security, unbounded keys,
    from bilateral k-Lin and k'-Lin, for (x, (z₁, z₂)) ↦ (z₁ ⊗ z₂) f(x)^⊤ with f an ABP.
  - The building block's security is Theorem 1 (Appendix B), and partial garbling is Lemma 1
    (cited, not proved).
- **Gaps:**
  - G1, symmetric DLIN with k = k' = 2: bridged; GJLS21 Thm 10.3 and JLS26 Thm 5.1 assert it, and
    no hop uses asymmetry.
  - G2, the class: bridged by z₁ = z₂ = y.
  - G3, adaptivity: Def 4.3 is a special case.
  - G5, correctness: perfect ⇒ Def 4.2.
  - G6, efficiency: written in Phase A.
  - **G4: Wee20's simulator needs g^µ, while Def 4.3 read literally gives e(g,g)^µ.** It is bridged
    by giving µ ∈ ℤ_p, which is what GJLS21 Thm 9.2's proof supplies. This needs a ruling (Q1).
  - **G7: partial garbling has no staged source.** This needs a ruling (Q2).

## Open questions (design-r2 § 7; recommended option first)

- **Q1**, the simulator's input per key: **(A) µ ∈ ℤ_p** / (B) literal G_T (unproved) / (C) g^µ.
- **Q2**, partial garbling: **(A) interface + instance in this job, after staging [AGW20] and
  [IW14]** / (B) interface only / (C) none (breaks Def 4.6).
- **Q3**, which notion each layer proves: **(A) the weakest that suffice (Def 4.3 outer,
  group-first Π)** / (B) Wee20's semi-adaptive / (C) monolithic.
- **Q4**, one job or two: **(A) one job, PARTIAL final allowed** / (B) two jobs.
- **Q5**, where `ReductionFn`/`NUPPT.Realizes` live: **(A) in house at `<BASE>`, shared with the
  sPRG job** / (B) private per job / (C) inline.

r1's Q1–Q5, Q7–Q12 and Q14 are settled by the sources and rulings (design-r2 § 7, table); r1's Q6
and Q13 continue as Q3 and Q4.

## Before dispatch (maintainer and Seyoon)

1. **Rulings** on Q1–Q5. Record them in `briefs/io-components/phfe/rulings.md`, with a
   decision-log row in `IOComponentsPlan.md`.
2. **Sources.** Stage on the exchange at `outbox/io-components/sources/`, with a `SHA256SUMS`
   whose hashes match `sources-r2.md` § 1:
   - the three PDFs: GJLS21 `481f999a…6eed`, Wee20 `d4def6b0…112a`, JLS26 `bb357e8d…2f3d`;
   - [AGW20] and [IW14], if Q2(A).
3. **`<BASE>`.**
   - Q5(A): the maintainer writes the realiser file in house, stacked on `foundations/subexp`
     (#374). `<BASE>` is that branch's head.
   - Otherwise `<BASE>` is `foundations/subexp`'s head.
   - Name the branch in `rulings.md`.
4. **Fill the placeholders** in `dispatch-prompt-r2.md`: `<BASE>`, `<RECORDS>` (the commit carrying
   this folder with `rulings.md`), `<EXCHANGE>` (the staging commit), all full hashes. Edit the
   `[Qn]`-marked items if a ruling differs from the recommended option.
5. **Check the host plan** with the sPRG job's dispatch: 3 Lean processes on the Mac in all. This
   job holds 1, so the sPRG job may hold at most 2. Both use `lean-slot.sh` with distinct tags.
6. Commit and push the records, push the exchange staging, and then the prompt is **Ready to
   dispatch**.
