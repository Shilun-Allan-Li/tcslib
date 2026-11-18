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
| `rulings.md` | **every ruling in force** for this job (decision-log rows of 2026-11-18, rule 15, Q-E1 (A), the source rule, the base); it takes precedence over every other file here |
| `sources-r3.md` | **r3.** All five PDFs with SHA-256 (AGW20 `b74c2ac9…d11f`, IW14 `ef6c7c6a…5e77` new); pins for [AGW20] §4.1–§4.2, Lemma 2, App. A (28)–(32), App. B, and [IW14] Def 1, Thm 3, Cor 1, §4.2; **what [Wee20, Lemma 1] needs and where it is proved**; the L₀/L₁ shapes settled (W1 inherited from AGW20 Lemma 2); **the instance chosen** (the layered ABP of a polynomial vector, AGW20 App. A = IW14 §4.2 at t = 1, path-sum proofs, exact privacy); misprints W1–W5 and readings R1–R4; G3, G4, G7 updated |
| `design-r3.md` | **r3.** What changed; rulings (§ 0); **rule 15** (§ 1E: raw bundles vs efficient interfaces, field forms, targets, assembly, the L1 link); deliverable, layout; realisers at two levels with the shared `RealizesOn`, `runDet`, R-DLOG, the vacuity rule (§ 4.4); the semi-adaptive notion and **the derivation of Def 4.3** (§ 4.5); partial garbling interface and layered instance (§ 4.7); semi-adaptive Π (Lemma 3 by an exact change of variables) and quadratic layer (§ 4.8); headlines on raw bundles and primitives (§ 4.10); milestones, size, **statements-gate order** (§ 6); questions (§ 7); risks |
| `duplication-sweep-r3.md` | **r3.** Amended r2 rows; the shared realisation API (§ 0b); adaptive games and deterministic runs (§ 3b); Mathlib for the layered garbling and Lemma 3 (§ 5b); `UniformSampler` as a type for rule 15 |
| `dispatch-prompt-r3.md` | **r3.** The prompt Seyoon pastes into Codex (Phase A); base filled (`iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`); one placeholder left, `dbea2807532392781304e004715f3b0190025f5e`; the `[Q-E1]` items take the must-reuse arm |
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
- **Q-E1 ruled (A)** (with the sPRG pack's Q-E1): `SamplesEfficiently` lives in the shared
  in-house `TCSlib/Cryptography/CoinSampling/Contract.lean` (`foundations/coin-contract`
  `8e01b720`), which is at the base; must-reuse, with `DrawSamplable`, `CoreComputable`, their
  readers and closure (`../contract/REPORT.md`). Disclosed limits: no product-of-draws sampler
  (Phase B), and the unused `Fintype` binder was dropped.
- **Sources:** no PDF is committed or pushed anywhere (pairing ruling Q12 (A); the ePrint PDFs
  are not ours to redistribute). Seyoon gives Codex a local folder with the five PDFs when he
  dispatches; the prompt pins each SHA-256 (as `sources-r3.md` § 1). Nothing is staged on the
  exchange; delivery is unchanged (`inbox/fills/io-phfe/`).

## Before dispatch (maintainer and Seyoon)

1. Done: Q-E1 (A) and its file; the base `iO/phase-a-base` at
   `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (#374, #378, the contract, #380; shared with the
   sPRG job; `../contract/REPORT.md`); `rulings.md`; the base filled in the prompt; the source
   rule applied (no staging).
2. Commit this folder (with `rulings.md`) and a decision-log row in `IOComponentsPlan.md`; put
   that commit in `dbea2807532392781304e004715f3b0190025f5e` (`git rev-parse`, full hash) and push the records.
3. Seyoon prepares the local source folder with `gjls21.pdf`, `wee20.pdf`, `jls26.pdf`,
   `agw20.pdf` and `iw14.pdf` (hashes in `sources-r3.md` § 1 and the prompt) and names it when he
   dispatches.
4. **Check the host plan** with the sPRG job's dispatch: 3 Lean processes on the Mac in all,
   this job 1, the sPRG job 1. Both use `lean-slot.sh` with distinct tags. The host addendum and
   `lean-slot.sh` hash to `02a6af16…` and `ff64d8d5…` at the exchange commit the prompt pins
   (`bc9d982b83cb35ea351e2fb373752e8688945b1c`).
5. Then the prompt is **Ready to dispatch**.
