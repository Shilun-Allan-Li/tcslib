This is the statement-phase PR of the pairing campaign (`PairingCryptographyPlan.md`). Seyoon ruled Q1–Q13, the location of IBE and G40-01 on 2026-11-16. It formalizes:
- **abstract symmetric bilinear groups** from a uniform PPT generator, with the BDH and decisional BDH (DBDH) assumptions;
- **Joux's one-round tripartite Diffie–Hellman** [Jou00];
- **Boneh–Boyen selective-ID IBE (BB1)** in the standard model [BB04, ePrint 2004/172, §4].

**Head:** `9e7a96481785d6cac4dea3b2e990c49ac278b060`. **Base:** `cryptography/pass-shelat-ch2-4`; the merge base is `673a2715`, and since then the branch has changed records only. The diff is #331's 13 files (+2293/−0).

## Modules
- `Pairing/{Group,Assumptions,Operations}.lean` and the `Pairing.lean` facade.
- `KeyExchange/Joux.lean` and its facade.
- `AdvancedEncryption/IdentityBased/{Defs,BonehBoyen,BonehBoyenSecurity,BonehBoyenMachine}.lean` and the `AdvancedEncryption/IdentityBased.lean` facade. The `AdvancedEncryption.lean` facade, shared with GSW, imports and lists both `Homomorphic` and `IdentityBased`.
- Root exports: `Pairing` and `KeyExchange` (the root already imports `AdvancedEncryption`).

Every file is under 1000 lines (the largest is `BonehBoyen.lean`, 677), and every line is at most 100 characters.

## Proved here
- Bilinearity, symmetry and non-degeneracy readers.
- Joux correctness ([Jou00, p. 388]), and key indistinguishability under DBDH (`jouxGame_eq_dbdhGame`). Joux states no security theorem; this result formalizes his §5 remark.
- BB1 correctness ([BB04, §4.1]).
- The injectivity of BB1's encodings on reachable objects: `bb1_encPP_inj`, `bb1_encSK_inj`, `bb1_encCT_inj`, which give `bb1Scheme`'s fields `encPP_inj`, `encSK_inj`, `encCT_inj` (ruling G40-01).
- `bb1_sidSecure` ([BB04, Theorem 4.1] at depth 1), derived from the targets below.

## Targets (`sorry`, with proof sketches)
- **T1** `bdhAssumption_of_dbdhAssumption`, a folklore result.
- **T2** `bb1_sim_real`.
- **T3** `bb1_sim_random`.
- **T4** `exists_bb1_distinguisher`, in its own module `BonehBoyenMachine.lean` (ruling Q11).

The fill units are `pair-bdh` (T1), `bb1-sim` (T2 and T3) and `bb1-machine` (T4). The last two own disjoint files and can run in parallel.

## History since Gate 40 round 1 (at `110c2f9d`)
- **LE-gate40** `3f9c49e5`, with the proof fix `70c1f444`:
  - **G40-01** (ruling: injectivity fields): `IBEScheme` gains `encPP_inj`, `encSK_inj` and `encCT_inj`. They state that the wire encodings are injective on the parameters of setup outputs, and on the keys and ciphertexts reachable under one setup output. This is not efficient decoding (Q5) and not global injectivity. BB1 proves them.
  - **G40-03, G40-04, G40-05**, docstrings only: explicit sampler parameters in the T4 sketch; T4's source tag; T1 described as independently derived folklore; `bilinear_pow` as the natural-exponent reader; `**Proof sketch.**` markers on `decrypt_encrypt` and `bb1_correct`.
- **Merge** `39d42e23` (signed) of the branch tip `673a2715`, which contains #332 and #333. The shared `TCSlib.lean` and `AdvancedEncryption.lean` are resolved by their union, and nothing else changes.
- **LE-doc-abs** `9e7a9648`, docstring only: [BB04, §3.1] writes the decision advantage with an absolute value (per the DW-7 transcription).

## Checks
- **Build of the head on the branch tip** (merge `39d42e23`; LE-doc-abs is docstring only):
  - the closure of root `TCSlib` and both `Checks` is 1299 modules; **661/661** rebuilt modules give rc 0 with 0 errors, and the whole-tree check passes;
  - admissions go **237 → 241**: T1–T4 only.
- **LE-gate40 build:** the 20-module pairing closure gives **20/20** rc 0.
- **Axioms:** Joux's results, `bb1_correct` and the three `bb1_enc*_inj` use the standard axioms only. Each of T1–T4 is the only `sorryAx` user in its closure, and `bb1_sidSecure` inherits exactly T2–T4.
- **Rule 10:** the canonical suite was run on **10** owners: the 8 modules with declarations (`Group`, `Assumptions`, `Operations`, `Joux`, `Defs`, `BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity`) and the `IdentityBased` and `AdvancedEncryption` facades. The other three changed files (`Pairing.lean`, `KeyExchange.lean` and the root) contain imports only.
  - Seals strict A/B and coe A/B: **40/40** probes pass.
  - Paired controls: 43 sealed negatives each fail exactly once, and their readers pass (ALL_OK).
  - Explicit-unfold scan: 0 foreign unfolds.
  - In round 1 the canonical suite covered only 3 modules (12 probes); the other modules had hand-list probes.
- **Lint:** no FAIL. There are two check-8 WARNs, `SIDSecure` and `BDHAssumption`/`DBDHAssumption`. They are false positives of the acronym heuristic: the readers `sidSecure_iff`, `bdhAssumption_iff` and `dbdhAssumption_iff` exist.

**Disclosed deviations from the papers** (see the plan, § Sources, and the docstrings):
- the single-point Joux form, which non-degeneracy permits;
- BB1 is the depth-1 instance of BB04's HIBE;
- the IBE advantage is twice BB04's;
- the statements are asymptotic rather than concrete;
- the challenger answers forbidden queries with `⊥`;
- the encodings are injective on reachable objects (G40-01).

## Gate 40
- **Round 1** (Codex, at `110c2f9d`): **HOLD**, with 0 blockers, 2 majors and 4 minors. No mathematical defect was found, and T1–T4 were judged true and sufficient.
- The resolutions are in `briefs/pairings/gates/40-pairings-statements/resolutions-r1.md`. LE-gate40 fixes G40-01 to G40-05; G40-06 is this description and the README.
- **Round 2** (Codex) is staged at this head (`pack-r2.md`) and **pending**.

The evidence is in `briefs/pairings/gates/40-pairings-statements/` (`landing-r1/`, `integration-tip/`). Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
