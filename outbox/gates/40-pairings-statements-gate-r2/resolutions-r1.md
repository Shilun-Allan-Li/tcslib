# Gate 40 · resolutions, round 1 · HOLD → round 2 staged

Codex's verdict is **HOLD**: 0 blockers, 2 majors, 4 minors, 0 notes.
- **Findings:** `findings/gate40-pairings-statements-findings.md`, SHA-256
  `ceb63bfc9c309eca34d3aef1f57cae0e636082a3b7d7ec2aeef99d4f06edd670`.
- **Audited head:** `110c2f9db810d243693b9a5e8976a5ad205f1bab`, records `356321ac`, exchange `870bed6c`, PR merge base
  `523d80d2`.

Codex found no mathematical defect in the completed proofs and no counterexample to T1–T4. It confirmed:
- T1–T4 are true on their sketched routes, and T2–T4 imply `bb1_sidSecure` with exactly its stated hypotheses (`H`,
  `O`, `hN`, `h`): the nine-game chain gives `2δ + 4σ + dbdhAdv D₀ + dbdhAdv D₁`; T1 is not used.
- The bundle, the generator, BDH and DBDH, the selective-ID handler, BB1 and the simulator agree with [BB04] and
  [Jou00] under rulings Q1–Q13 and the location ruling; sampling `Setup` before the run is distributionally valid for
  every adversary.
- The completed proofs are correct: the group facts, Joux correctness, `jouxGame_eq_dbdhGame` (its final `rfl` reads
  only the local `jouxMsg`), `jouxKeyIndist_of_dbdhAssumption`, `BB1.decrypt_encrypt`, `bb1_correct`, the 21 case
  readers and `bb1_sidSecure` from T2–T4.
- Every public definition has a reader; no new `@[simp]`. The layering, the three fill units (disjoint owned files),
  the facades, widths and imports satisfy the rulings and policy. No duplicate public result.

| # | Severity | Disposition |
|---|---|---|
| G40-01 | major | **Fixed by LE-gate40** under **ruling G40-01 (Seyoon, 2026-11-16): injectivity fields.** `IBEScheme` gains `encPP_inj` (the parameter encoding is injective on the parameters of setup outputs), `encSK_inj` and `encCT_inj` (the key and ciphertext encodings are injective on the keys and ciphertexts reachable under one setup output), with a **Deviation** sentence in the structure docstring: fidelity is injectivity on reachable objects, not efficient decoding (Q5) and not global injectivity. Round 1's countermodel violates `encCT_inj` (its two reachable ciphertexts share the encoding), so it is no longer an `IBEScheme`. `bb1Scheme` proves the three fields from the new public lemmas `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj` (each with a proof sketch; standard axioms); no new admission, and T1–T4 and `bb1_sidSecure` are unchanged. Commits `3f9c49e573fe56ac72c33a3f960f4229a29a9a5e` and `70c1f44432a41bcdb6f6d8602d957d2fc68ce0da` (a two-line proof fix). Evidence: `landing-r1/gate40-le-evidence.zip` (SHA-256 `5be013be1aeb4dd8feb0f3f1f458b1fd0bbab882df80048e2bd043eadbb1d7d5`): 20/20 modules rc 0 on the base; 384 constants in the axiom census, `sorryAx` only in T1–T4 and `bb1_sidSecure`; and the build of the head on the tip (below). |
| G40-02 | major | **Fixed by LE-gate40** (evidence only). The canonical suite was run at `70c1f444` on 10 owners: `Pairing/Group`, `Pairing/Assumptions`, `Pairing/Operations`, `KeyExchange/Joux`, `IdentityBased/Defs`, `IdentityBased/BonehBoyen`, `IdentityBased/BonehBoyenMachine`, `IdentityBased/BonehBoyenSecurity`, and the `IdentityBased` and `AdvancedEncryption` facades. The other three changed files (`Pairing.lean`, `KeyExchange.lean`, `TCSlib.lean`) contain imports only. Term-collected, closure-complete seals strict A/B and coe A/B: 40/40 probes rc 0, 0 errors, install and EOF records, no failing declaration. Paired controls, strict and coe: 43 sealed negatives each fail exactly once, 43 readers pass, unsealed probes pass, ALL_OK True. Explicit-unfold scan: 164 items, 0 foreign (8 same-file definitions). Same evidence ZIP. |
| G40-03 | minor | **Fixed by LE-gate40** (docstring only, code-identical). T4's sketch gives `n = κ + wG(κ) + 1`, draws by `(sampleBelowL p (Nat.size p) n n w).getD 0` on independent `n²`-bit blocks, `p ≤ 2^{wG} < 2^n` and `0 < p`, error `(1/2)^n ≤ 2^{−κ}` per draw and `σ = (q + 1) · 2^{−κ}`; it also states the modular arithmetic through `H` and `exists_toCompOn_of_toComp`. T4's statement is unchanged. |
| G40-04 | minor | **Fixed by LE-gate40** (docstrings only, code-identical). T4 tagged [BB04, §4.2, the algorithm `B` in the proof of Theorem 4.1]; T1's source line now describes the implication as independently derived folklore, with [BB04, §3.1] defining the two problems; `Group.lean` (module, `BilinearGroup`, `bilinear_pow`) distinguishes the natural-exponent reader from the signed-exponent law, which follows from the homomorphism fields. |
| G40-05 | minor | **Fixed by LE-gate40.** `BB1.decrypt_encrypt` and `bb1_correct` mark their proof paragraphs `**Proof sketch.**`. |
| G40-06 | minor | **Fixed in the records; the PR-description part is drafted.** The pairings README's current checkpoint was refreshed at records `4f416a8f6f8381fb48aee44b4d7670a135e7fa7d` (head `110c2f9d`, base `523d80d2`, the hold and ruling, the seal coverage stated explicitly); historical entries are kept. The replacement PR description `pr-description-r2.md` states the head, the history and the coverage per module; the maintainer applies it to #331 before round 2 is dispatched. The README's checkpoint has to be refreshed again to the round-2 head (`pack-r2.md`, known slips). |

Since LE-gate40 the head also took a signed merge of the records tip, `39d42e235a62b7085ffc19b01f371015c20d7795` (#332
and #333 merged; the shared facades `TCSlib.lean` and `AdvancedEncryption.lean` resolved by the filed union; diff
against the tip = #331's 13 files), and **LE-doc-abs** `9e7a96481785d6cac4dea3b2e990c49ac278b060` (docstring only:
[BB04, §3.1] writes the decision advantage with an absolute value, per the DW-7 transcription). The build of the merge
on the tip (`integration-tip/int-331-tip-evidence.zip`, SHA-256
`3227f70b77ce455994efe86c90f2fb6b2e3bf8b16a2fffa7508f1a87a6662eb8`): 661/661 rc 0 over the 1299-module closure,
admissions 237 → 241 (T1–T4 only), standard axioms for the proved results and the three new lemmas, whole-tree check
OK. This discharges round 1's merge conditions (#333 merged first; #331 took the union; the merged tree was rebuilt).

**Notes carried to the fill briefs (not round-2 items).** T2 (`bb1-sim`): `ProbComp.expect_simulate_congr` has one
state type, so the fill reduces to a common augmented state with the existing abstraction and eager-sampling APIs, or
requests a shared relational lemma in `Games` (not a private BB1 host). T4 (`bb1-machine`): the sampler parameters of
G40-03, modular negation and subtraction through `ArithmeticFP`'s natural-number functions, `xgcd` with `0⁻¹ = 0`, and
`exists_toCompOn_of_toComp` for the handler theorem.

**Round 2 staged:** `pack-r2.md` and the round-2 files beside it (`SHA256SUMS-r2`); the Codex prompt is
`dispatch-r2.md`.

**Next:** Gate 40 round 2 (Codex) at `9e7a96481785d6cac4dea3b2e990c49ac278b060`.
