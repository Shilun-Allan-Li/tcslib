# io-phfe: dispatch pack (degree-2 PHFE from DLIN, [Wee20] in the JLS26 pipeline)

The second iO-components job (IOComponentsPlan.md): one end-to-end Codex job in a local checkout,
**Phase A**.
- Explicit functions, correctness, security inequalities.
- Efficiency is baked into the interface definitions and written as targets, not proved.
- A statements gate on its checkpoint 0 and a proofs gate on its final.
- Static only; nothing is committed or dispatched.

Revisions:
- **r1** was prepared 2026-11-18 at records `0fec2589`, blocked on sources.
- **r2** was prepared 2026-11-18 at records `1a9a3295`, from the three staged PDFs and the
  rulings then.
- **r3** (current) was prepared 2026-11-18 at records `32a40963`. It applies:
  - the Phase A rulings (Q1 A, Q2 A, Q3 = Wee20's semi-adaptive notion for both layers, Q4 A,
    Q5 A);
  - the partial-garbling sources [AGW20] and [IW14];
  - the shared `Asymptotic/Realization.lean` (`cdc0934f`);
  - #378 (`51dc7672`);
  - **standing rule 15** (efficiency mandatory and baked into definitions).

  r3 is a delta: the r3 files amend the r2 files, which stay binding where not amended. The r3
  prompt is complete.

## Contents

| File | What |
|---|---|
| `sources-r3.md` | **r3.** All five PDFs with SHA-256 (AGW20 `b74c2ac9…d11f`, IW14 `ef6c7c6a…5e77` new); pins for [AGW20] §4.1–§4.2, Lemma 2, App. A (28)–(32), App. B, and [IW14] Def 1, Thm 3, Cor 1, §4.2; **what [Wee20, Lemma 1] needs and where it is proved**; the L₀/L₁ shapes settled (W1 inherited from AGW20 Lemma 2); **the instance chosen** (the layered ABP of a polynomial vector, AGW20 App. A = IW14 §4.2 at t = 1, path-sum proofs, exact privacy); misprints W1–W5 and readings R1–R4; G3, G4, G7 updated |
| `design-r3.md` | **r3.** What changed; rulings (§ 0); **rule 15** (§ 1E: raw bundles vs efficient interfaces, field forms, targets, assembly, the L1 link); deliverable, layout; realisers at two levels with the shared `RealizesOn`, `runDet`, R-DLOG, the vacuity rule (§ 4.4); the semi-adaptive notion and **the derivation of Def 4.3** (§ 4.5); partial garbling interface and layered instance (§ 4.7); semi-adaptive Π (Lemma 3 by an exact change of variables) and quadratic layer (§ 4.8); headlines on raw bundles and primitives (§ 4.10); milestones, size, **statements-gate order** (§ 6); questions (§ 7); risks |
| `duplication-sweep-r3.md` | **r3.** Amended r2 rows; the shared realisation API (§ 0b); adaptive games and deterministic runs (§ 3b); Mathlib for the layered garbling and Lemma 3 (§ 5b); `UniformSampler` as a type for rule 15 |
| `dispatch-prompt-r3.md` | **r3.** The prompt Seyoon pastes into Codex (Phase A), with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>` and one item marked `[Q-E1]` |
| `sources-r2.md`, `design-r2.md`, `duplication-sweep-r2.md` | r2; binding wherever r3 does not amend them |
| `dispatch-prompt-r2.md` | r2 prompt (superseded) |
| `sources.md`, `design-r1.md`, `duplication-sweep.md`, `dispatch-prompt.md` | r1, kept for the record |

## The deliverable in brief

- **Target.** [GJLS21, Def 4.3] (ε = 1, many-key), for the class of [GJLS21, §9], with Defs 4.1,
  4.2 and 4.6. It is **derived** from Wee20's semi-adaptive notion by a generic game identity
  (`simAdv_eq_saSimAdv`). Wee20's semi-adaptive notion is proved for both layers (Q3).
- **Rule 15.**
  - `FEScheme`, `Simulator`, `SASimulator` and `PartialGarbling` carry efficiency fields:
    uniform `PolyTimeComputable` cores with pp on the input, and samplers via #378's
    `UniformSampler`.
  - The constructions are raw bundles (`wee20PHFE_raw`, …), proved correct and secure.
  - The primitives (`wee20PHFE … hT`, `wee20Sim`, `layeredPG`) are assembled from the targets
    `Wee20.Targets`.
  - The L1 realisers (DLIN ⇒ MDDH) follow from a pre-processing target in Phase A
    (`mddhRealizable_of_preTarget`).
- **Partial garbling** (Q2).
  - The interface is [Wee20, Lemma 1] = [AGW20, Lemma 2], with shapes L₁ ∈ ℤ_p^{t×mn},
    L₀ ∈ ℤ_p^{t×m} and t = m + n′ − 1.
  - The instance is [AGW20, App. A, (28)–(32)] on the layered ABP of f(x) = C·x̂^{⊗d}, proved by
    path sums with **exact** privacy: ≈ 500–1,000 lines plus a 200–330-line interface (r2:
    1,200–2,500).
  - m and t depend only on (ℓ, d, n′), so Wee20's "same m for all keys" holds.
- **Reductions.** Every reduction is in the shared `RealizesOn` form (body: encoded challenges
  and layout-length coin strings only). There are two levels:
  - L1: one activation of an MDDH distinguisher;
  - L2: the adaptive adversary run against deterministic answers (`runDet`).

## Size

≈ 8,800–16,100 Lean lines (central ≈ 12,000); r2 was 7,400–13,800. Against r2:
- Q3 (B) adds +1,300–2,500;
- rule 15 adds +700–1,200;
- the layered instance saves −700 to −1,500;
- the shared realisation file saves 0–150.

One job, PARTIAL final allowed (Q4 A).

## Questions

- **Settled:** Q1 (A) µ ∈ ℤ_p; Q2 (A) interface + proved instance; Q3 Wee20's semi-adaptive for
  both layers, Def 4.3 derived; Q4 (A) one job; Q5 (A) the shared `RealizesOn`; rule 15.
- **Open** (design-r3 § 7.2; the same as the sPRG pack's Q-E1; rule them together):
  - **Q-E1**, where `SamplesEfficiently` lives:
    - **(A) a shared in-house `CoinSampling/Contract.lean` stacked into `<BASE>`**
      (recommended);
    - (B) one per job, unified later;
    - (C) inline fields.

## Before dispatch (maintainer and Seyoon)

1. **Ruling on Q-E1.** Record it with Q1–Q5 and rule 15 in `briefs/io-components/phfe/rulings.md`,
   with a decision-log row in `IOComponentsPlan.md`. If (A), write
   `TCSlib/Cryptography/CoinSampling/Contract.lean` in house (sPRG design-r3 § 1.2's
   declaration, with readers, ≈ 60–120 lines, on #378).
2. **`<BASE>`**, shared with the sPRG job: one branch stacking:
   - #374 (`cbce64d1`);
   - `foundations/realization` (`cdc0934f`);
   - #378 (`51dc7672`);
   - the Q-E1 file, if (A).

   The first two merge with no conflict (ref-free `git merge-tree`; see the sPRG README).
   Elaborate the new files with one Lean process, and push it. Name the branch in `rulings.md`.
3. **Sources.** Stage on the exchange at `outbox/io-components/sources/`, with a `SHA256SUMS`
   whose hashes match `sources-r3.md` § 1: GJLS21, Wee20, JLS26 (shared with io-sprg), AGW20 and
   IW14.
4. **Fill the placeholders** in `dispatch-prompt-r3.md`: `<BASE>`, `<RECORDS>` (the commit
   carrying this folder with `rulings.md`) and `<EXCHANGE>` (the staging commit), all full
   hashes. Edit the `[Q-E1]` item if the ruling is not (A).
5. **Check the host plan** with the sPRG job's dispatch: 3 Lean processes on the Mac in all,
   this job 1, the sPRG job 1. Both use `lean-slot.sh` with distinct tags. The host addendum and
   `lean-slot.sh` hash to `02a6af16…` and `ff64d8d5…` at the exchange tip of 2026-11-18.
6. Commit and push the records, push the exchange staging, and then the prompt is **Ready to
   dispatch**.
