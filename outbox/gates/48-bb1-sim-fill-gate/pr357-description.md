This is the landing PR for the pairing fill `bb1-sim` (`PairingCryptographyPlan.md`). It proves **T2** `bb1_sim_real` and **T3** `bb1_sim_random` (`AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean`) and the two `Games/Relational.lean` targets `ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel`. With T1 (#340) and T4 (#346) merged, **Boneh–Boyen BB1's selective-ID security `bb1_sidSecure` now uses only the standard axioms**, and its `sorryAx` trace is empty [BB04, Theorem 4.1].

**Head:** `7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff`. **Base:** `cryptography/pass-shelat-ch2-4` (records tip `e1d39836`, whose Lean equals the #346 merge `3f540c22`). No stacking: #340 and #346 are merged.

## Scope (9 files, against the tip)
- **`Games/Relational.lean`:** the bodies of `expect_simulate_rel` (induction on the computation, generalizing both states) and `expect_sample_rel` (one bijective coupling of a sample). Headers, statement prose and sketches are frozen and byte-identical; `prob_simulate_rel` is unchanged.
- **`BonehBoyenSecurity.lean`:** the bodies of T2 and T3, five helper imports and a `## Contents` section. The target headers and prose, and `bb1_sidSecure` whole, are byte-identical.
- **Five new helper modules** under `IdentityBased/BonehBoyenSecurity/`: `Lazy` (lazy simulator handlers), `Real` (the real game with `h` recorded and drawn late), `Coupling` (step M of design r1 §3.1), `Random` (the T3 comparison) and `Chain` (the T2 chain `prob_sidGame_coins`). 130–565 lines each; all under the 1000-line cap and 100-character lines.
- **The ten approved readers** (Seyoon, 2026-11-17) as verbatim pure insertions into the frozen files:
  - six in `Defs.lean`: `IBEScheme.sidImpl_zero_onSpec`, `sidImpl_two_onSpec`, `sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec`, `sidImpl_challenge_fresh_onSpec`;
  - four in `BonehBoyen.lean`: `bb1Scheme_setup_eq`, `bb1Scheme_keyGen_bind`, `bb1Scheme_enc_bind`, `ofFn_bb1Scheme_encCT`.

  Removing the two blocks restores both files byte for byte (insertion pins `97ecb6e0…` for `Defs.lean`, 563 lines, and `88454d6f…` for `BonehBoyen.lean`, 760 lines).

## Commits (5, all SSH-signed)
- The external worker's four commits (Claude; sub-agent A wrote `Coupling.lean`), maintainer-signed `git cherry-pick -S` copies of `23614c0a`, `3f430cae`, `622f5b03` and `c35595ae`: the readers, the `Relational` bodies, the helper modules, and T2/T3. `git range-diff` against the reproduced worker series is 4/4 `=`.
- **LE-bsf1** (maintainer landing edit, ruling Q2), byte-identical to the phase-1 review's `le-bsf1-proposed.diff` (3 files: `Lazy`, `Real`, `Coupling`). It closes BSF-F02/F03 (checkpoint C1-F03/F04):
  - `BB1Sim.bb1RealState_eq … := rfl`, the reader of the public abbrev `BB1RealState` (policy §1);
  - "Glue:" notes on the 21 helper docstrings that had neither a `[BB04, …]` tag nor a glue note, and the formulas of `bb1SimLazy_eq` and `BB1RealState`;
  - `bb1RealAt` and `bb1RealLazy` now say "a variant of the game of [BB04, §2.1]".

  No statement or proof changes apart from the one added declaration.

## Overlap and reuse
- **DL-57 (accepted by Seyoon, Q1; cleanup Stage 2).** The public `BB1Sim.sidSpec_rng_one`/`_two` (`BonehBoyenSecurity/Lazy.lean`) have the same statements and proofs as T4's **private** `BB1Machine.sidSpec_rng_one'`/`_two'` (`BonehBoyenMachine/Oracles.lean`). Stage 2 promotes the scheme-generic `sidSpec_dom_*`/`sidSpec_rng_*` and `zeroBits_eq_cast` into `IdentityBased/Defs.lean` as `IBEScheme.*` and re-points both users, proof-only. `sidImpl_allOutputs_some` and `sidImpl_none_of_ne` travel with the same promotion (BSF-F07).
- The rest is reuse, as disclosed: T2 uses Mathlib's `CharP.natCast_injOn_Iio` directly (BS-F01), the averaging bound `abs_expect_sub_le_expect`, `Games.expect_simulate_eager`, `Bridge.expect_sample_pair` and the `Pairing/Group` helpers. Every `expect_simulate_rel`/`expect_simulate_eager` use is a single application; no new eager or relational lemma (DL-33). The review's own searches found no undisclosed duplicate of a public lemma.
- **`RealReads` has no paired control (BSF-F05, accepted):** it is a `Prop` structure whose readers are its projections; its constructor is sealed in `BonehBoyenSecurity` and the consumers' seals pass.

## Checks
- **Landing (static).** decls2 (pinned) against the tip: **69 ADDED** (10 readers, 58 `BB1Sim.*` helpers, `bb1RealState_eq`), **0 CHANGED, 0 REMOVED**. Reader insertion check against the tip: PASS with 12 controls, pins unchanged. Frozen-header check: 12/12 PASS with 8 controls. Hygiene: 0 `sorry`/`admit`/`native_decide`/`axiom` tokens, no line over 100 characters, every helper docstring tagged or glued.
- **Phase 2 (Lean, maintainer, on olean snapshot #5).** `cp -al` of the snapshot, then the recipe:
  - **19/19 modules rc 0**, 0 `error:`/`error(`, 0 `sorry` warnings (the 9 files, `Games`, the five `BonehBoyenMachine` helpers and facade, the `IdentityBased`/`AdvancedEncryption` facades and root `TCSlib`); sources bound 19/19. State check **1432/1432 OK**; all 19 rebuilt oleans have link count 1; snapshot #5 rehashes 0/0/0 before and after.
  - **Admissions against the tip: 196 → 192, exactly −4** (`expect_simulate_rel`, `expect_sample_rel`, T2, T3).
  - **Axioms:** 76 constants (every new one, the four targets, `prob_simulate_rel`, `bb1_sidSecure`, T4) all standard; census over the 9 owners 325 constants, 0 non-standard. **`#sorry_trace` is empty for `bb1_sidSecure`** (closure 20,373 constants) and for the five other roots; a sorry control is caught by both the trace and the axiom check.
  - **Rule 10:** canonical seals A and B, strict and coe, on all 9 owners (`Relational`, `Defs`, `BonehBoyen`, `BonehBoyenSecurity` and the 5 helpers): **36/36 with 0 errors**, request counts equal to the delivered table (LE-bsf1 adds no definition). Paired controls (32 probes per harness, the 10 reader pairs and the 5 helper-definition pairs): **ALL_OK in strict and coe**, 485 sealed negatives each failing exactly once, every positive and unsealed probe clean. `bb1RealState_eq`: the abbrev `BB1RealState` is never requested by a seal (notation), so it has no sealed negative; its reader and `rfl` entries pass in 6 sealed and 6 unsealed probes per harness.
  - **Explicit-unfold scan:** 527 items, **0 foreign**.
  - **Lint:** `campaign_style_lint --check8b` 92 FAIL / 104 WARN over 529 files, the tip's FAIL/WARN line set unchanged (0 new, 0 gone); `style_lint` 0 findings; `sk15`'s one finding is the base's `bb1SimChal_fresh`.

## Review (`briefs/pairings/fills/bb1-sim/fill-final-r1/review.md`, `phase2.md`): ACCEPT WITH LANDING EDITS
- **Phase 1 (static):** 0 blockers, 0 majors; minors BSF-F01 (the signed exchange final; process only), F02 and F03 (closed by LE-bsf1), F04 (closed by DL-57); infos F05–F08. The patch series reproduces, the readers are verbatim, and the worker's evidence recounts clean (36 head and 16 base seals with 0 errors, 485 sealed negatives per variant each failing once).
- **Phase 2 (Lean on this head):** PASS (above). Final verdict: **ACCEPT WITH LANDING EDITS (LE-bsf1 applied)**.

## Gate
**The bb1-sim gate audits it** (the ten readers and the T2/T3 fill), per the design rulings (Q8).

Seyoon merges.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA