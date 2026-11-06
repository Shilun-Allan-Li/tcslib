# Fill col-b (the `col_zk` ladder): REPORT (final)

## Environment and base

- Base: `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit, head of PR #210). The local branch `fill/col-b`
  was created there and never pushed or rebased. Its 11 commits are in `patches/`.
- I ran as an **internal worker** under the environment note `issue/internal-env.md`. There was no preflight and no
  cache step; the olean tree was pre-built. At start the machine had `nproc` 4 and 16 GB RAM (about 15 GB available).
  Each module was checked with `scripts/lean_check_tree.sh`, one Lean process at a time, and `lake build` was never run.
- Module check times at the final head (`evidence/sweep.log`): ColZKLemmas 5 s, ColZKMachine 4 s, Simulator 16 s.
  The downstream modules took 2–34 s each (Universal 34 s, EXP 28 s).
- Exchange commits: checkpoint 1 `1ca1b9f8`, checkpoint 2 `c6f3f809`, checkpoint 3 `8683b838`, checkpoint 4
  `02d040ef`, checkpoint 5 `c2fde31a`; final: the commit that carries this file.

## Targets

**`col_zk` is partial.** Its `sorry` is unchanged, and no new `sorry` was added.
- The whole assembly is proved, sorry-free, as the private `colZK_zk_of_eqs (hmsg) (hidx) (hC) : ZK (colProtocol Com ℓ) R3COL`.
- It is conditional on two equations that are not published at the base (E-API, below):
  - `hmsg : ∀ w i, msgAt w i = pairFstD (pairSndD^[i] w)`;
  - `hidx : ∀ m w, edgeIdxOfMsg m w = w.length % m`.
- **Frontier (one line).** Once the two equations land as `msgAt_eq` and `edgeIdxOfMsg_eq`, the target is
  `col_zk hC := colZK_zk_of_eqs msgAt_eq edgeIdxOfMsg_eq hC`.
  - Both equations are `rfl` on their definitions.
  - `evidence/frontier-demo.log` shows that a scratch copy closes `col_zk` this way with `fun _ _ => rfl`, using only
    `propext, Classical.choice, Quot.sound`. That demonstration reads the bodies and is **not** delivered.

| Step | Lemma(s) | Status |
|---|---|---|
| 1 | `statClose_sampleColorPair` | filled (see the editing slip below) |
| 4 | `exists_colSimRed_fixCoins`, `colSimRed_fixed_eq` | filled |
| 5 | `ColZK.hidingView` (+ `_eq`), `ColZK.polyTimeComputable_hidingView`, `ColZK.exists_colHidingRed`, `ColZK.distAdv_distinguisherL_reparam`; the identification `colZK_planted_eq` in `Simulator.lean` | machine, coin transport and hiding bound **filled**; the planted-case identification is **blocked (E-API)** and proved conditionally on `hmsg`, `hidx`. The edgeless identification (`hidingView_edgelessAdv`) needs neither equation. |
| 2 | `statClose_colRealView` | filled |
| 3 | `statClose_colSim_colSimTrunc` | filled |
| 6 | `exists_colZK_edgeless` | filled |
| 7 | `col_zk` | partial: `colZK_zk_of_eqs` (conditional, sorry-free); frontier above |

- **Editing slip.** `statClose_sampleColorPair` was named in commit `cd39e4c8`, but the text did not reach the file.
  It is therefore missing from the sources of checkpoints 1 and 2. It was restored in `7a592167`; checkpoints 3–5
  and the final delivery contain it.
- **Binder change, no content change.** `statClose_colRealView`'s hypothesis `hc` is unused by the proof, so it is
  bound as `_hc`; the statement is otherwise the brief's.
- **Step 5 interface.** `ColZK.hidingView` takes only `V'`: the endpoint commitments are precomputed in the advice, so
  neither `Com` nor `ℓ` is needed. `exists_colHidingRed`'s statement is the brief's, with `hidingView V'` in place of
  `hidingView Com ℓ V'`.

## E-API (published interfaces missing at `16a7d02d`)

The planted attempt `colSimAttemptPlanted` reads the challenge through `msgAt cv i`, and its restart test is
`edgeIdxOfMsg m (V com ρ) = e₀`. A machine can only compute `pairFstD (pairSndD^[i] cv)` and `|reply| % m`. To
identify the machine's view with the planted attempt, the proof must read one of these definitions through an
equation, and none is published.

| Definition (file) | Lemma needed (`rfl` on the definition) | Alternative |
|---|---|---|
| `msgAt` (`ThreeColoring/Protocol.lean`, col-a's file) | `msgAt_eq : msgAt w i = pairFstD (pairSndD^[i] w)` | `multiCom_eq` in `Commitment.lean`: `multiCom Com v r = Strategy.encodeMsgs (List.ofFn fun i => Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))))`, with the identification restricted to `multiCom` samples |
| `edgeIdxOfMsg` (`ThreeColoring/Language.lean`) | `edgeIdxOfMsg_eq : edgeIdxOfMsg m w = w.length % m` | none |

- **Blocked:** the step-5 identification for `m > 0`, and with it the last line of step 7.
- **Not added, bodies not read** in the delivered code.
- The pre-ship route probe sealed `multiCom` but not this splice: the string function was left to the fill. This is a
  finding against the brief's prerequisite table, not against pack 03g's statements; the targets remain provable as
  stated.

## New declarations

`Simulator.lean` is the owned file; all its new lemmas sit in sections with the variables `{Com} {ℓ}`.

**Public lemmas in `Simulator.lean`:**
- `statClose_sampleColorPair` (step 1);
- `exists_colSimRed_fixCoins`, `colSimRed_fixed_eq` (step 4);
- `statClose_colRealView` (step 2);
- `statClose_colSim_colSimTrunc` (step 3);
- `exists_colZK_edgeless` (step 6).

**Private helpers in `Simulator.lean` (prefix `colZK_`):**
- `colZK_sampleColorPair_take`: the sampler reads only the first `3T` bits;
- `colZK_planted_eq`: the conditional identification of step 5;
- `colZK_length_colOpen`, `colZK_length_view_le`, `colZK_attempt_some`: advice-length facts;
- `colZK_planted_case`: the `m > 0` bound;
- `colZK_zk_of_eqs`: the assembly.

**New helper module `ThreeColoring/ColZKLemmas.lean`** (342 lines, namespace `TCSlib.Cryptography.ColZK`, all
public, no definitions):
- uniform tape fields: `pushesUniform_restrict`, `table_index_lt`, `table_index_inj`, `pushesUniform_offsetTable`,
  `pushesUniform_blockFields`;
- averaging: `acceptProb_comp_pushesUniform`, `exists_fixSeed`, `acceptProb_seed_to_coins`, `distAdv_seed_to_coins`,
  `distAdv_le_one`;
- tape lists: `ofFn_drop_take`, `ofFn_drop_eq`, `ofFn_take_drop`;
- searches: `findSome?_map_option`, `findSome?_range_eq_finRange`, `findSome?_finRange_split`,
  `findSome?_finRange_split_lt`;
- the error's negligibility: `negligible_colZKErr`, which takes `Negligible (εB ∘ Nat.sqrt)` because
  `Negligible.comp_sqrt` stays in `Simulator.lean`.

**New helper module `ThreeColoring/ColZKMachine.lean`** (422 lines, namespace `TCSlib.Cryptography.ColZK`):
- definitions, each with its equation lemma and no `@[simp]`: `hidingView` (`hidingView_eq`), `edgelessAdv`
  (`edgelessAdv_eq`), `plantedAdv` (`plantedAdv_eq`);
- parsing: `field_encodeMsgs`, `field_zero_encodeMsgs`;
- the view on its two kinds of advice: `hidingView_edgelessAdv`, `hidingView_plantedAdv_some`,
  `hidingView_plantedAdv_none`;
- polynomial time: `polyTimeComputable_next` (the generic one-call lemma, via P12), `polyTimeComputable_hidingView`;
- the machine and its coins: `exists_colHidingRed` (step 5, the probe-R4 shape), `distAdv_distinguisherL_reparam`
  (coin transport), `distAdv_distinguisherL_congr` (moves `D` along `|encGraph G| = n²`; the brief's `finCongr`
  point);
- `exists_hidingView_bound`: the worst data at each `n`, the machine, the coin transport and `multiHiding` with
  `rw [PolyExpr.eval_var] at`, giving a negligible `ε ≥ 0`;
- advice lengths: `length_edgelessAdv_le`, `length_plantedAdv_le`;
- one private helper, `colZK_field_poly`.

**Line counts and size.**
- `Simulator.lean` is **1659 lines**, against 804 at the base and a target of at most 1000 (reported under the brief's
  "if so, with the reason").
- **Why it is over.** By the brief's placement rule, every statement that names
  `colSim`/`colSimTrunc*`/`colRealView`/`colSimRed`/`colSimAttempt*` must stay in this file: steps 1–4 and 6, the
  identification and the `m > 0` bound. Their proofs unfold those definitions:
  - `colSim`/`colSimAttemptStr` block by block in step 3;
  - the edgeless branch in step 6;
  - the attempts' outputs in the advice bound.
- All the generic material (tape fields, averaging, searches, the machine, the hiding bound and the negligibility)
  went to the two helpers, about 760 lines.
- `Protocol.lean` is not touched.

## The error accounting used (binding route, R2-1)

- **`n = 0`:** `Δ ≤ 1 ≤ ε 0 = 2` (`ColZK.distAdv_le_one`).
- **`m = 0`, `n ≥ 1`:** `Δ ≤ 4^{-N} + ε_B(n)`, one multi-value gap (R2-1); then `ε_B(n) ≤ N² ε_B(n)`.
- **`m > 0`:** `Δ ≤ 4^{-N} + K(2^{-N} + 4^{-N}) + K ε_B(n) + e^{-n}`, from `(1 − 1/m)^{nm} ≤ e^{−n}`. Then `K ≤ N²`
  and `√N = n`.
- **The error function:** `ε N := N² ε_B(√N) + e^{−√N} + N²((1/2)^N + (1/4)^N) + (1/4)^N`.
  - This is the binding one.
  - `ε_B ≥ 0` is built into `exists_hidingView_bound`, which returns `|ε_B'|`.
- **The advice bound (R2-2 form).** Every field of either kind of advice is at most
  `M(n) = 4n² + 2Lz(n²) + 2·V'.coins(n²) + 2n(2C(2n+3+ℓ(n))^d + 2) + 2(3ℓ(n)+20) + 12 + C(2n+3+ℓ(n))^d + n + 1`,
  with `|Com w| ≤ C(|w|+1)^d`. The bound is `b = 15(2M + 2)` (`CommitmentLemmas.length_encodeMsgs_le`).

## Requested shared lemmas, reuse screen and copies

**Requested for promotion:**
- `ColZK.distAdv_distinguisherL_reparam`, the two-parameter coin transport, `distAdv` form. It should be placed next to
  `CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`. There is no private copy, and the optional `acceptProb` form
  was not added.
- `ColZK.distAdv_distinguisherL_congr`.
- `ColZK.polyTimeComputable_next`: the generic form of `ColSimMachine.reply_poly`, which is not duplicated; the brief
  authorizes it.

**Disclosed copy:** `ColZK.pushesUniform_restrict` is `Asymptotic/MultiMessage.lean`'s `pushesUniform_comp_injective`,
generalized from `Fin (q+1)` to any finite `J`, with the same proof. `MultiMessage` is not upstream of
`Simulator.lean`, so it could not be imported. It should replace the original (the original is the special case).

**Inline parse, no named shadow.** `hidingView` parses its advice and the challenge with `pairFstD (pairSndD^[i] ·)`,
which is `msgAt`'s body written inline. This is why the E-API arises.

**No private cited from another file.**
- Public lemmas used from `ColProofs` (`ProtocolProofs.lean`): `sampleEdgeIdx_ofFn_castLE` and `ofFn_getD_lt`. They
  are about `Language`/core definitions, not shadows.
- Public lemmas used from `ColMachines` (`Machines.lean`):
  - lengths and edges: `edgeCount_eq`, `countTrue_le`, `encColor_eq`, `edgeAt_eq_some_of_pos`;
  - polynomial time and message lists: `iterSnd_poly`, `polyTimeComputable_flatMap_range`,
    `encodeMsgs_ofFn_eq_flatMap`, `getD_eq_pairFstD_iterate`.

**Mathlib.** No new roots. `List.finite_length_le` is outside the import closure, so it was avoided
(`Finite.exists_max` on `Σ k : Fin (b+1), Fin k → Bool`).

## Rule-10 seal (`evidence/seal.log`, `evidence/seal/mkseal.py`, `evidence/seal/names2.txt`)

- **Sealed names:** 57 foreign definitions marked `attribute [local irreducible]` (listed in the log):
  - probability and experiments: `StatClose`, `uprob`, `uexp`, `acceptProb`, `distAdv`, `PushesUniform`;
  - samplers: `rejectionSample`, `sampleIdx`, `sampleEdgeIdx`, `samplePerm3`;
  - graphs and colours: `edgeIdxOfMsg`, `msgAt`, `edgeAt`, `edgeOf`, `edgeList`, `padColor`, `encColor`;
  - the protocol: `multiCom`, `colCommit`, `colOpen`, `colCoinSlice`, `colIterations`, `colProver`, `colProtocol`;
  - interaction: `withV`, `viewV`, `View.encode`, `exec`, `moverIsV`, `Strategy.*`;
  - definitions and encodings: `ZK`, `R3COL`, `ProperColoring`, `Negligible`, the graph and colouring encoders and
    decoders;
  - machines: `NUPPT.*`, `PolyExpr.eval`/`subst`/`normal`, `pairEncode`/`pairFstD`/`pairSndD`, `countTrue`,
    `mergeAt`.
- **Where the seal goes.** In each helper, after `open`. In `Simulator.lean`, inside the ladder and assembly sections
  and around step 1, so the pre-existing proofs are not sealed.
- **Controls.** In each block, `edgeIdxOfMsg` and `msgAt` are read by `rfl`.
- **Result.** Sealed: the only errors are the controls, which fail. Unsealed: no errors, and the controls pass.
- **Violations found and fixed by the first sealed run.**
  - `acceptProb` read by `rfl` in `exists_fixSeed` and in two `e1`/`e2` steps; now read through `acceptProb_def`.
  - `StatClose` built as a bare function in `distAdv_le_one` and `hW`; now through `statClose_iff`.
  - `ProperColoring` built as a bare function in step 6; now through `ProperColoring_iff`.

## Final checks

- **Sweep** (`evidence/sweep.log`): ColZKLemmas, ColZKMachine, then order-list lines 127–142, from `Simulator` to
  `ZeroKnowledge`. All have status 0. The only sorry warning in my files is `col_zk`'s.
- **Axioms** (`evidence/axioms.log`):
  - every new public lemma, and the private `colZK_zk_of_eqs`, `colZK_planted_case` and `colZK_planted_eq`: at most
    `propext, Classical.choice, Quot.sound`;
  - `col_zk`, `col_hvzk`, `col_zeroKnowledgeProof` and `zk_proof_of_levinReduction` (`NP.lean`): `sorryAx` in
    addition, from `col_zk`'s remaining `sorry` and col-a's targets.
- **Lint before** (`evidence/lint-before.log`): `style_lint` 0 findings on `Simulator.lean`; campaign lint 9 FAIL
  (6 facade on `ThreeColoring.lean`), 26 WARN.
- **Lint after** (`evidence/lint-after.log`):
  - `style_lint`: one finding on the three files, `Simulator.lean` at 1660 lines over 1000. This is the size finding
    reported above.
  - Campaign lint: 11 FAIL, 27 WARN. The added items are two facade FAILs (`ColZKLemmas`, `ColZKMachine`; expected)
    and the `Simulator.lean` size WARN.
  - No new check-8 name (`Simulator.lean` 16 names, one fewer than at the base). The helpers have no check-8 WARN.

## Diff and landing edits

- The diff touches only `ThreeColoring/Simulator.lean` and the two new helper modules.
- **Facade edit for the maintainer:** add `import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas` and
  `import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKMachine` to `ThreeColoring.lean`, with their two
  `## Contents` lines.
- **Docstring edits to `col_zk`:**
  - the required R2-1 replacement. ", so the hiding terms are at most …" became ". The hiding term is …", so the
    sentence before it now ends with a period;
  - the optional M3 sync: `statClose_sampleColorPair` is now named, and "still to be added …" is removed.
  - The ladder lemma names were not added to the sketch steps (optional), and nothing else changed.
