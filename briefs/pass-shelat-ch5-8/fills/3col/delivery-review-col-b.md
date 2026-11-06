# Delivery review: fill unit col-b (the `col_zk` ladder)

- **Delivery:** `inbox/fills/col-b/` on `exchange/pass-shelat-ch5-8` at
  `35acfadb3a9db6dacdb959b8e1f270468fb14358` (REPORT.md, 11 patches, `src/`, `evidence/`). The
  exchange checkout was pulled to `a8f0347c`; the folder is unchanged since `35acfadb`.
- **Worker branch:** `fill/col-b`, head `240075b6bc0183f29e1df4403e5695dcfe713d60`, base
  `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit; it is also the merge base), 11 commits.
- **Brief:** `brief-issued.md`, unit col-b, with `review.md`. **Policy:** `policy.md`.
- **Reviewed:** 2026-11-06. This was an independent run:
  - the patches were replayed in a fresh scratch worktree;
  - Lean ran against a copy of the worker's olean tree, one process at a time, never `lake build`
    or `lake exe cache get`;
  - the seal names were collected from the elaborated terms of every new constant, not from the
    worker's list.

## Verdict: **land after edits**, including the conditional frontier edit

All ladder steps are proved and sorry-free:
- steps 1–6: `statClose_sampleColorPair`, `exists_colSimRed_fixCoins`, `colSimRed_fixed_eq`,
  `statClose_colRealView`, `statClose_colSim_colSimTrunc`, the step-5 machine
  (`ColZK.exists_colHidingRed`, the coin transport, `ColZK.exists_hidingView_bound`) and
  `exists_colZK_edgeless`;
- the assembly, as the private `colZK_zk_of_eqs`.

The assembly is conditional on two equations that are not published at the base, so `col_zk`
keeps its `sorry`. This is the E-API escalation the brief asks for. It is real: no published
lemma reads `edgeIdxOfMsg` in general (finding 9).

The other checks pass:
- the statements are frozen;
- the downstream modules and `audits/pass-shelat/Checks` elaborate;
- all 137 new constants are standard-axiom-only;
- the rule-10 seal holds under this review's own list (54 names in `Simulator.lean`, 21 and 7 in
  the helpers), and `msgAt`/`edgeIdxOfMsg` are sealed in every region.

With stub lemmas of exactly #210's next-round statements placed beside their definitions, the
one-line frontier `col_zk hC := colZK_zk_of_eqs msgAt_eq edgeIdxOfMsg_eq hC` elaborates sealed.
`col_zk` and `col_hvzk` then print `[propext, Classical.choice, Quot.sound]`.

There are **no blockers and no majors**. The edits are minor:
- **E1** is the facade landing edit;
- **E3, E4** replace two undisclosed copies of core and library lemmas with citations;
- **E2, E5, E6** are a stale name, layout and a source tag;
- **E7** is the conditional frontier edit, applied once #210's next round lands.

The size of `Simulator.lean` (1659 lines, no exception) needs a maintainer decision (finding 4).
The disclosure ledger is amended (D1).

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | `git am` of the 11 patches onto `16a7d02d` in the fresh worktree `$SP/wt-rev-colb` (with `.lake/packages` linked): clean (`am.log` empty). The result's tree `943f6d12…` equals the tree of `240075b6`. All three files match `src/` and the `fill/col-b` head byte for byte (`cmp`). **Files changed** (`diffstat.txt`): `ThreeColoring/Simulator.lean` (modified, +863 −4), `ThreeColoring/ColZKLemmas.lean` (new, 342 lines), `ThreeColoring/ColZKMachine.lean` (new, 422 lines). That is `3 files changed, 1623 insertions(+), 4 deletions(-)`. The only removed lines are the four docstring lines of `col_zk` (finding 2). `src/` holds exactly these three files. |
| 2 | Statement freeze and scope | `declfreeze.log`: all 45 base declarations of `Simulator.lean` are present, in their base order, with byte-identical headers. The only changed docstring is `col_zk`'s, and it changed only by the two brief-authorized edits (finding 2). No base proof changed; the two "PROOF-CHANGED" lines of the script are inserted section headers after `exists_colSimulator` and `Negligible.comp_sqrt`, at declaration boundaries. Base sorries in the owned file: 1; at the head: 1, the same `col_zk` `sorry`. **New in `Simulator.lean` (13):** the six ladder lemmas the brief names, all public, and seven `private` helpers prefixed `colZK_`. They sit in `section ColZKLadder` and `section ColZKAssembly` with the brief's variables `{Com} {ℓ}`, and step 1 sits beside `sampleColorPair`. The ladder statements are compared with the brief's code blocks in `briefstmt.py`: steps 1, 3, 4 and 6 are identical, and `colSimRed_fixed_eq`'s equation is the brief's. Step 2 differs only by `hc` → `_hc`, and step 5 only by `hidingView V'` in place of `hidingView Com ℓ V'` (finding 2). **Helpers:** both are in namespace `TCSlib.Cryptography.ColZK`, between 150 and 600 lines, with the full policy §1 header. They contain 37 public declarations (18 and 19) and one `private` (`ColZK.colZK_field_poly`). Their three definitions `hidingView`, `edgelessAdv` and `plantedAdv` each have an `_eq` lemma, and none is `@[simp]`. The helpers have no check-8 WARN and add no `@[simp]`, `attribute` or `set_option` beyond the standard header. |
| 3 | Elaboration | `scripts/lean_check_tree.sh`, `TCSLIB_OLEANS=$SP/rev-colb-oleans`, in order (`module-checks.log`): `ColZKLemmas` 6 s, `ColZKMachine` 3 s, `Simulator` 18 s, facade `ThreeColoring` 2 s, `NP` 12 s, facade `ZeroKnowledge` 3 s, `audits/pass-shelat/Checks` 130 s. All exit 0, with 0 errors. The only warning is `col_zk`'s `sorry`. The downstream set (`downstream.py` over the brief's order list) is `Simulator`, `ThreeColoring`, `NP`, `ZeroKnowledge`, plus `Checks`; `NPLemmas` and order lines 130–141 do not import `Simulator`. |
| 3 | Axioms | `axioms.log`: `#print axioms` for the six ladder lemmas, `ColZK.exists_colHidingRed`, `ColZK.distAdv_distinguisherL_reparam`, `ColZK.exists_hidingView_bound` and `ColZK.polyTimeComputable_hidingView` gives `[propext, Classical.choice, Quot.sound]`. A `collectAxioms` sweep over all **137** new constants (both helper modules, the 13 new `Simulator` declarations and their auxiliaries, private ones included) finds **0** non-standard. That covers `colZK_zk_of_eqs`, `colZK_planted_case` and `colZK_planted_eq`. `col_zk` and its consumers print `sorryAx` (`module-checks.log`, the `Checks` lines 367–373), from `col_zk`'s own `sorry` and col-a's targets. |
| 3 | Facade | Proposed edit E1, checked as part of `edited-checks.log`: all seven modules exit 0. `campaign_style_lint.py --check8b TCSlib/Cryptography/ZeroKnowledge`: 11 FAIL / 27 WARN at the head, and 9 FAIL / 27 WARN with E1, which is exactly the base's six `ThreeColoring.lean` facade FAILs (`campaign-lint-{head,edited}.log`). |
| 4 | Rule 10 under this review's seal | See finding 9. The names were collected by a meta probe (`probe/Collect.lean`, `collect.log`) over the 137 constants. It takes the TCSlib definitions of other modules that occur in their elaborated types and values, excluding reducible ones and instances, and widens with the statements of every constant used and the bodies of own-module definitions used. A second probe (`matchers.log`) finds **no foreign compiler-generated matcher** and no foreign auxiliary constant beyond the helpers' own `_proof_n` (and `CommitmentLemmas.ofFn_eq_append_cons._proof_1`). No sealable name is `@[simp]`. `PolyExpr.eval` is left unsealed by ruling Q1, so the lists exclude it. **`ColZKLemmas` (7):** `HardcoreBit.PushesUniform`, `Negligible`, `StatClose`, `acceptProb`, `distAdv`, `uexp`, `uprob`. **`ColZKMachine` (21):** `NUPPT.Uniform/coinLen/distinguisherL/layout/output/runAt/runAtL`, `PolyExpr.subst`, `PolyTimeComputable`, `pairFstD`, `pairSndD`, `EncodingMachines.modNum`, `Negligible`, `Strategy.Efficient/encodeMsgs/ofNUPPT`, `View.encode`, `acceptProb`, `distAdv`, `multiCom`, `Turing.pairEncode`. **`Simulator` (54):** see `seal/names-Simulator-all.txt`. It contains `msgAt`, `edgeIdxOfMsg`, the helpers' `ColZK.hidingView/edgelessAdv/plantedAdv`, `colProver`, `colProtocol`, `colCommit`, `colOpen`, `colCoinSlice`, `colIterations`, the samplers, `Protocol.viewV/withV/withV_vCoinsEquiv`, `View.encode`, `exec`, `moverIsV`, `ZK`, `R3COL`, `ProperColoring`, `NUPPT.simulate` and the rest. **Seal placement** (`seal/mkseal.py`): the whole file after `open` in each helper. In `Simulator.lean` the seal covers three regions: step 1 with `colZK_sampleColorPair_take`, the ladder section and the assembly section; the base proofs stay unsealed. **Results:** all three files elaborate sealed with exactly the controls as errors (`RevSealed*.out`), and unsealed with no error (`RevControl*.out`). Sealing `PolyExpr.eval` as well changes nothing (`RevSealedEval*.out`). **Controls:** `distAdv` by its body (both helpers) and `multiCom` by its body (`ColZKMachine`). In each `Simulator` region, `edgeIdxOfMsg`, `msgAt` and `edgelessAdv` are read by their bodies. Each closes unsealed and fails sealed with "Type mismatch". **Explicit unfolds:** every `unfold` in the added code names an own-file definition (`sampleColorPair`, `colSimRed`, `firstSome`, `colRealView`, `colSimBlock`, `colSimCoins`, `colSimAttemptStr`, `colSimAttempt`, `colSim`, `colSimTrunc`, `colSimAttemptPlanted`, `colSimAttemptH/W`). There is no `show`, `delta` or `change` on a foreign body. The four bare `simp`/`simpa`, run through `simp?`, use core and Mathlib lemmas only (`simpq.log`). |
| 5 | Duplication | See findings 5 and 6. |
| 5 | Lint and size | `style_lint.py` on the three files: one finding, the size of `Simulator.lean` (`style-lint-head.log`); with E1–E6 the same single finding (`style-lint-edited.log`). Every proof over 20 lines has a **Proof sketch.** (`prooflen.py`): `statClose_colSim_colSimTrunc` 122 lines, `exists_colZK_edgeless` 123, `colZK_planted_case` 124, `colZK_zk_of_eqs` 83, `statClose_colRealView` 52, `polyTimeComputable_hidingView` 37, `pushesUniform_blockFields` 27, `exists_hidingView_bound` 27, `colZK_planted_eq` 23, `colSimRed_fixed_eq` 22, `length_plantedAdv_le` 22. **Sizes:** `Simulator.lean` 1659 lines (804 at the base; 1660 with E1–E7), `ColZKLemmas.lean` 342 (328 with E3–E4), `ColZKMachine.lean` 422. |
| 6 | Frontier | See finding 10. |
| 7 | Routes, sketches, docstrings | See findings 11 and 12. |

## Findings

1. **note: integrity.** The replay is clean and equals both `src/` and the worker head (check 1).
   The diff touches only the owned file and the two new helper modules, as the REPORT says.

2. **note: the declared deviations and the authorized docstring edits are confirmed.**
   - **`_hc`.** `statClose_colRealView`'s properness hypothesis is not used by its proof, because
     the closeness of the real view to `colRealView` holds for any colouring. Naming it `_hc`
     changes no type: binder names are irrelevant up to α-equivalence. All callers pass it
     positionally. The rename only keeps the unused-variable linter quiet: an unused named
     binder of a declaration signature warns, as the review's own control `example`s show in
     `RevControlSimulator.out`. Accepted.
   - **`ColZK.hidingView V'`.** The brief gave only an interface, "it cannot be stated exactly
     before its string function is designed". The endpoint commitments `A₁, A₂` are fields of
     the advice, so `Com` and `ℓ` are not needed. `exists_colHidingRed` is otherwise the brief's
     statement verbatim. Accepted.
   - **The extra definitions `edgelessAdv` and `plantedAdv`.** These are new string functions of
     the kind the brief's "what it may hold" list allows. Each has an `_eq` lemma, neither is
     `@[simp]`, and neither copies a definition of the owned file.
   - **`col_zk`'s docstring.** The R2-1 replacement is the brief's text verbatim. The sentence
     before it ends with a period instead of ", so", which the replacement requires. The M3
     sync removes the clause "still to be added: …"; the lemma name was already in place.
     Nothing else in the docstring changed.

3. **note: the editing slip is confirmed and harmless.** Patch 0001 (`cd39e4c8`) names
   `statClose_sampleColorPair` in its subject but adds no such declaration, and no use of it.
   Patch 0004 (`7a592167`) adds it. The exchange sources of checkpoints 1 (`1ca1b9f8`) and 2
   (`c6f3f809`) lack it; checkpoints 3–5 and the final delivery contain it. The first use is in
   patch 0005 (step 3), after the restore. The final tree is unaffected, so no edit is needed.
   If the series is landed commit by commit, the subject of 0001 overstates its content.

4. **minor: `Simulator.lean` is 1659 lines, with no approved exception.** The brief says it
   "should stay at or under 1000". The user's size exception covers `Protocol.lean` only. The
   REPORT reports the size and gives the reason: the placement rule keeps every statement that
   names the simulator definitions in this file. The reason holds, and a helper module cannot
   absorb more:
   - the helpers are upstream of the owned file;
   - `col_zk`, whose position is frozen, consumes the whole ladder.

   Only the two `colOpen`/`colCommit` length helpers (about 25 lines) could move to a helper.
   **Maintainer decision, not a landing condition.** Either record a size exception for
   `ThreeColoring/Simulator.lean`, as for `Protocol.lean`, or plan a split at the next statement
   window. Two splits are possible: move the simulator definitions (base lines 1–715) to an
   upstream `SimulatorDefs.lean`, or move `col_zk`/`col_hvzk`/`col_zeroKnowledgeProof` with the
   ladder to a downstream module. Either one moves frozen declarations.

5. **minor: two undisclosed copies of published lemmas (edits E3 and E4).**
   - **`ColZK.acceptProb_seed_to_coins`** is the public `TCSlib.Cryptography.acceptProb_bind`
     (`Pseudorandom/Indistinguishability.lean`, in the import closure) read right to left: same
     samplers, same distinguisher, same proof idea (`Equiv.prodAssoc`). **E4** deletes it and
     proves `distAdv_seed_to_coins` by `rw [distAdv_def, distAdv_def, acceptProb_bind,
     acceptProb_bind]`. The only other user is `distAdv_seed_to_coins`, and `acceptProb` is
     already sealed, so E4 adds no foreign reading.
   - **`ColZK.findSome?_map_option`** is core's `List.map_findSome?` reversed, with
     `Option.map g ∘ f` written pointwise; its proof re-does the induction. **E3** keeps the name,
     because `statClose_colSim_colSimTrunc` rewrites with the pointwise form, which
     `← List.map_findSome?` does not match syntactically. It replaces the proof by
     `List.map_findSome?.symm`.

   Both edits were checked unsealed (`edited-checks.log`) and sealed
   (`RevSealedEdited{ColZKLemmas,Simulator}.out`: only the controls fail).

6. **minor: the reuse disclosure is incomplete (D1, ledger).** The REPORT's disclosed copy is
   confirmed. `ColZK.pushesUniform_restrict` is `MultiMessage.pushesUniform_comp_injective`
   generalized from `Fin (q+1)` to any finite `J`. It has the same `Equiv.ofInjective` /
   `Equiv.Set.sumCompl` / `Equiv.sumArrowEquivProdArrow` proof, and `MultiMessage` is outside
   the closure. Not disclosed (none is verbatim, and replacing them is optional):
   - **Cross-unit.** dl-a's private `dla_pushesUniform_restrict` is a third copy of the same
     construction (dl-a review, finding 5). The three `pushesUniform_castLE` copies in
     `GraphIsomorphism/Proofs.lean`, `GraphIsomorphismZK/Closeness.lean` and
     `ThreeColoring/ProtocolProofs.lean` are special cases. One public
     `HardcoreBit.pushesUniform_restrict`, which dl-a also requested, would retire all of them.
   - **`ColZK.table_index_lt` and `table_index_inj`.** These are the range and injectivity of
     Mathlib's `finProdFinEquiv` (`i·k + j`, written `j + k·i` there). The library already has
     the decoding form `EnsembleLemmas.finProdFinEquiv_symm_mk`.
   - **`ColZK.ofFn_drop_take`, `ofFn_drop_eq` and `ofFn_take_drop`.** These are general-offset
     forms of `EnsembleLemmas.take_drop_ofFn_blocks`, `OneWay.ofFn_block_eq_take_drop` and
     `OneWay.ofFn_castLE_eq_take`. The last one is used by step 2 itself.
   - **`ColZK.polyTimeComputable_next`.** It is the brief-authorized generic lemma. Its proof is
     `ColSimMachine.reply_poly`'s, line for line, with the tape generic. `reply_poly` and the
     inline step of `GraphIsomorphismZK/Simulator.lean` (line 345) are now special cases. The
     REPORT's "not duplicated" holds only in the sense that `reply_poly` itself was not copied.
   - **`ColZK.distAdv_seed_to_coins`.** It has the content of `distAdv_sunglassRed`. That lemma
     cannot be cited under rule 10, because `sunglassRed` and `pushSampler` have no published
     equations. This is a request for the Indistinguishability owner.
   - **`ColZK.field_encodeMsgs`.** It restates `ColMachines.getD_eq_pairFstD_iterate`, reversed.
   - **Dependence on the shadow file.** `statClose_colSim_colSimTrunc` and `exists_colZK_edgeless`
     use `ColProofs.sampleEdgeIdx_ofFn_castLE` and `ColProofs.ofFn_getD_lt`
     (`ProtocolProofs.lean`). Both are about the original `sampleEdgeIdx` and core lists, not
     about shadows, and nothing is transferred by `rfl`: the seal with `sampleEdgeIdx` passes.
     This is allowed. If the dedup queue retires `ProtocolProofs.lean`, these two lemmas must
     move first.

   The REPORT's three promotion requests are endorsed:
   - `ColZK.distAdv_distinguisherL_reparam`, next to
     `CommitmentLemmas.acceptProb_distinguisherL_of_runAtL`;
   - `ColZK.distAdv_distinguisherL_congr`;
   - `ColZK.polyTimeComputable_next`, with `reply_poly` re-derived from it.

7. **nit: a stale name in `ColZKLemmas`' module docstring.** The docstring cites
   `colZK_attempts_le`, which exists nowhere: the `K ≤ N²` bound is proved inline in
   `colZK_zk_of_eqs`. **E2** drops it.

8. **nit: layout and a source tag.** Two declarations in `Simulator.lean` are not separated by
   a blank line from the next docstring (after `colSimRed_fixed_eq` and after
   `statClose_colRealView`), and three blank lines follow `colZK_planted_case`. **E5** fixes
   both. `colSimRed_fixed_eq` is the only new ladder lemma whose docstring carries no
   `[PS10, …]` tag, only the label `(Claim-129.d)`; the brief asks for the tag. **E6** adds
   `[PS10, proof of Proposition 128.8, the reduction to the hiding property]`. The equation
   lemmas `hidingView_eq` and `plantedAdv_eq` point to their definitions' docstrings for the
   formula instead of stating it. The formula is the statement itself, so no edit is proposed.

9. **note: E-API and rule 10 confirmed; there are no other readings.**
   - **Neither body is read.** The delivered code reads neither `msgAt` nor `edgeIdxOfMsg`.
     Both are sealed in all three `Simulator` regions, the sealed file has no error beyond the
     controls, and neither name occurs in the helpers' terms. `colZK_planted_eq` uses the
     hypotheses `hmsg`/`hidx` only. `hidingView` writes `msgAt`'s body,
     `pairFstD (pairSndD^[i] cv)`, inline. That is the same expression, not a reading of the
     definition, and the REPORT discloses it.
   - **No other foreign definition is read** under the review's seal: no failure besides the
     controls, and no foreign matcher. The list of replacement lemmas is therefore empty apart
     from the two equations.
   - **The block is genuine.** The published readings of `edgeIdxOfMsg` are
     `edgeIdxOfMsg_edgeMsg` (`@[simp]`, challenges `1^e` only) and `edgeIdxOfMsg_lt`. Neither
     gives `|w| % m` for the verifier's arbitrary reply. So `edgeIdxOfMsg_eq` is needed whatever
     the route.
   - **`msgAt` alone is avoidable.** The REPORT's alternative is correct: `cv` is always a
     `multiCom` sample, and `ColSimLemmas.msgAt_multiCom` with `multiCom_eq` and
     `field_encodeMsgs` gives the identification on those samples. This does not unblock
     `col_zk`, so the two-equation frontier is the right one to land.
   - **This is a brief-preparation miss.** The prerequisite table (P1–P12) omits both equations.
     The pre-ship probe sealed `multiCom` but not the splice or the restart test. It is not a
     finding against pack 03g's statements.
   - **The worker's seal list** (57 names, one list for all files) is consistent with this
     review's list:
     - it omits `NUPPT.simulate`, `PolyTimeComputable` and `EncodingMachines.modNum`, and, in
       `Simulator.lean`, the helpers' own `hidingView`/`edgelessAdv`/`plantedAdv`;
     - it adds `perm3Equiv` and `ColSimLemmas.mergeAt`, which the new code does not read.

     With all of these sealed the result is the same. The worker sealed `PolyExpr.eval` as well,
     and so did this review's extra run; both pass.

10. **note: the frontier is checked (E7, conditional).** The setup:
    - stubs of exactly #210's next-round statements, explicit binders in definition-argument
      order, placed beside their definitions (`edits/frontier-stubs-scratch.diff`; scratch
      only, not part of any landing):
      - `msgAt_eq (w : List Bool) (i : ℕ) : msgAt w i = pairFstD (pairSndD^[i] w)` in
        `Protocol.lean`, after `msgAt`;
      - `edgeIdxOfMsg_eq (m : ℕ) (w : List Bool) : edgeIdxOfMsg m w = w.length % m` in
        `Language.lean`, after `edgeIdxOfMsg`;
    - E1–E6 plus the frontier line.

    The checks, against the review's olean copy:
    - **Chain.** The whole chain was re-elaborated, from `Language` through `Machines`,
      `Parties`, `ProtocolProofs`, `Protocol`, `SimulatorLemmas`, `SimulatorNumeric`,
      `SimulatorMachine`, both helpers, `Simulator`, the facade, `NP` and `ZeroKnowledge` to
      `Checks`. All exit 0 with 0 errors (`edits/frontier-checks.log`, `frontier-checks2.log`
      for the final E7 text).
    - **Warnings.** `Simulator.lean` now has **0 warnings** (no `sorry`). `Protocol.lean` keeps
      col-a's two.
    - **Sealed.** The copy `seal/RevSealedFrontierSimulator.lean` adds a fourth seal region
      around `col_zk` with the same 54 names, `msgAt` and `edgeIdxOfMsg` included. It
      elaborates with only the controls failing, plus one deliberate failure, described next.
    - **Robust form.** `colZK_zk_of_eqs (fun _ _ => msgAt_eq ..) (fun _ _ => edgeIdxOfMsg_eq ..) hC`
      also closes. It closes against implicit-binder variants of the equations too, where the
      direct line fails; that is the deliberate failure, at line 1681. Use this form if the round
      publishes the lemmas with implicit binders or in another argument order.
    - **Axioms** (`edits/frontier-axioms.log`, `Checks` in `frontier-checks.log`): `col_zk` and
      `col_hvzk` print `[propext, Classical.choice, Quot.sound]`.
      `col_zeroKnowledgeProof` and the `NP.lean` wrappers keep `sorryAx`, from col-a's
      `colRep_efficientProverProof` only.
    - **Sketch.** Checked in finding 11.

11. **note: `col_zk`'s frozen proof sketch still describes the assembled proof.** Each step maps
    to a lemma:

    | Sketch step | Lemma or step in the proof |
    |---|---|
    | (1) | `statClose_colRealView` |
    | (2) | `statClose_colSim_colSimTrunc` |
    | (3) | `uprob_colSimTruncW_eq` (`hW`) |
    | (4) | `exists_colSimRed_fixCoins`, then `colSimRed_fixed_eq` |
    | (5) | `statClose_colSimTruncH` with `one_sub_inv_pow_mul_le_exp` |
    | the `m = 0` paragraph | `exists_colZK_edgeless` |
    | `n = 0` | `ColZK.distAdv_le_one` |
    | the hiding bound | `exists_hidingView_bound` |
    | the error | `ε` and its negligibility (`negligible_colZKErr`, `Negligible.comp_sqrt`) |
    | the triangle inequality | `distAdv_def`, `abs_sub_le` |

    Four machine-level details differ from the sketch, which is still true at the level it
    describes:
    - **The maximization.** It is over (vector, vector, advice of length at most `b(n)`), not
      over "the data". The bound `Lz` enters through `b`.
    - **`D`'s advice.** It is not part of `B`'s advice; `NUPPT.exists_comp` carries it.
    - **The machine shape.** It is the brief's R4 shape (`exists_comp`, `exists_reparam`,
      `exists_withAdvice`), not `NUPPT.exists_reparam_advice`. The brief allows either.
    - **The advice bound.** It comes from `length_multiCom_le`, `colOpen_eq` and
      `colZK_length_view_le`, not `colProtocol_proverBounded`.

    No edit is proposed: the sketch is frozen, and refreshing it needs docstring authorization,
    as in dl-a finding 7. The sketches of the new private helpers (`colZK_planted_case`,
    `colZK_zk_of_eqs`) give the assembly in detail.

12. **note: routes and sketches of the filled steps match their proofs.**
    - **Step 1.** It follows the brief's route: `statClose_rejectionSample 6 3 T` (`6 ≤ 2³`),
      the curried `finProdFinEquiv`, `sampleIdx_ofFn_eq_rejectionSample` (P11), `StatClose.map`,
      `comp_equiv_right` and `comp_equiv_left`.
    - **Step 4.** `exists_colSimRed_ge` with `exists_fixCoins`; the attempt table is nonempty
      from `m > 0` and `[Nonempty ρ]`. For `colSimRed_fixed_eq`, the sketch's split of
      `List.finRange N` at `k` is `ColZK.findSome?_finRange_split_lt`, which is built on
      `CommitmentLemmas.ofFn_eq_append_cons`.
    - **Step 5.** `NUPPT.exists_comp`, `exists_reparam (.mul .var .var)` and
      `exists_withAdvice`, as the sketch says. The coin transport is the brief's `distAdv`-level
      statement and proof (`NUPPT.coinLen_eq`, `PolyExpr.eval_subst/mul/var`, the `finCongr`
      reindexing). The hiding bound is `Finite.exists_max` on `Σ k : Fin (b+1), Fin k → Bool`,
      then `multiHiding .var`, `rw [PolyExpr.eval_var] at`, and `|ε_B|` (probes R3b and S3).
    - **Step 2.** `ColZK.pushesUniform_offsetTable` for the permutation trials and the
      commitment randomness at `3|x| + iℓ(n) + j`, inside the tape by `PolyExpr.eval_mono`.
      Then `statClose_samplePerm3`, `withV_vCoinsEquiv`, `viewV_withV`, `exec_succ` and the
      public `colProver` equations, both `m = 0` and `m > 0`.
    - **Step 3.** The four block fields (`pushesUniform_blockFields`); the edge sampler's prefix
      (`ColProofs.sampleEdgeIdx_ofFn_castLE`, `|E| ≤ n²`); the colour pair's `3|x|` bits
      (`colZK_sampleColorPair_take`); `OneWay.statClose_pi` over the `K` blocks
      (`colIterations_eq`, `colCoinSlice_eq`); and `edgeAt_eq_some_edgeOf`.
    - **Step 6.** The edgeless properness (from `mem_edgeList_iff`), step 2, the one-attempt
      branch (`colCommit_eq`), the π-average by the new `exists_fixSeed`, `distAdv_seed_to_coins`
      and `exists_fixCoins` for `r_V`, then the triangle inequality. One route difference: the
      brief says "fix π and then `r_V` by `exists_fixCoins`". π is a seed factor of the real
      side only, so `exists_fixCoins`, which fixes a distinguisher coin, does not apply to it.
      `exists_fixSeed` is the right tool, and the sketch says so.
    - **The error accounting** is the binding one (R2-1). The `m > 0` bound uses `e^{−n}` in
      place of `(1 − 1/m)^K`, and the advice bound is R2-2's with the extra fields in `M`.
    - **Docstrings.** Every new declaration has one. Every public one opens with a statement,
      and every nontrivial one carries a sketch.

13. **note: REPORT claims verified.** This review's own runs agree with the REPORT on these
    points:
    - the target and step statuses, and the 13 new `Simulator` declarations;
    - the line counts (342, 422 and 1659);
    - the sweep (status 0, a single `sorry` warning);
    - the axiom prints;
    - the lint lines: `style_lint` one size finding, and campaign lint 11 FAIL / 27 WARN, of
      which two facade FAILs are new;
    - check-8: `Simulator.lean` has 16 names (17 at the base; `colSimRed` gained
      `colSimRed_fixed_eq`), and the helpers have none;
    - no new Mathlib roots (the helpers import TCSlib modules only);
    - the seal after commit `613ef003` (no `acceptProb`, `StatClose` or `ProperColoring` body read);
    - the editing slip.

    The departures are findings 5 and 6, which concern the reuse screen.

## Landing edits (exact)

All diffs are under `$SP/review-colb/edits/`. They touch no statement and no base proof.
- **`landing-edits.diff` (E1–E6).** It touches `ThreeColoring.lean`, `ThreeColoring/ColZKLemmas.lean`
  and `ThreeColoring/Simulator.lean`. `git apply --check` is clean on the `fill/col-b` tree.
  - **Unsealed:** the edited `ColZKLemmas`, `ColZKMachine`, `Simulator`, facade `ThreeColoring`,
    `NP`, facade `ZeroKnowledge` and `Checks` all exit 0 with 0 errors (`edited-checks.log`).
  - **Sealed:** the edited `ColZKLemmas` and `Simulator` give only the controls as errors
    (`seal/RevSealedEdited*.out`).
  - **Lint:** `style_lint` reports the size line only. Campaign lint reports 9 FAIL, the base's
    six facade FAILs among them.
- **`frontier-edit.diff` (E7, conditional).** Apply it on top of E1–E6 once #210's next round
  has landed `msgAt_eq` and `edgeIdxOfMsg_eq`. `git apply --check` is clean after E1–E6.
  It was checked against the stubs (finding 10). Recheck it against the real lemmas when they
  land.

**E1** (facade). In `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean`, after
`import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol` insert

```lean
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ColZKMachine
```

and in `## Contents`, after the `Protocol` item (ending `(Prop-127.6).`), insert

```
* `ColZKLemmas` — generic lemmas of the `col_zk` ladder: disjoint fields of a uniform tape are
  independent and uniform, averaging over seeds, first-success searches split at an index, and
  the negligibility of the error of [PS10, Proposition 128.8].
* `ColZKMachine` — the hiding reduction of [PS10, proof of Proposition 128.8] with its attempt
  table fixed, as a machine (`hidingView`, `exists_colHidingRed`), the two-parameter coin
  transport and the hiding bound for all the fixed reductions at once.
```

**E2** (finding 7). In `ColZKLemmas.lean`'s module docstring, replace
``function (`negligible_colZKErr`, `colZK_attempts_le`).`` by ``function (`negligible_colZKErr`).``

**E3** (finding 5). In `ColZKLemmas.lean`, replace the docstring and proof of
`findSome?_map_option` (the statement is unchanged) by

```lean
/-- Mapping the values of a search: `l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g`
(core `List.map_findSome?`, read from right to left, with the composite written pointwise). -/
theorem findSome?_map_option {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g :=
  List.map_findSome?.symm
```

**E4** (finding 5). In `ColZKLemmas.lean`, delete `acceptProb_seed_to_coins` with its
docstring. In `distAdv_seed_to_coins`, replace ``(`acceptProb_seed_to_coins`)`` in the docstring
by ``(`acceptProb_bind` on both samplers)``, and replace the proof line by

```lean
  rw [distAdv_def, distAdv_def, acceptProb_bind, acceptProb_bind]
```

**E5** (finding 8). In `Simulator.lean`, insert a blank line before
`/-- **The real view is` and before `` /-- **`colSim` is ``. Reduce the three blank lines after
`    _ ≤ _ := by linarith [hexp]` to one.

**E6** (finding 8). In `Simulator.lean`, replace the first docstring line of `colSimRed_fixed_eq`
by

```
/-- **With the attempt table fixed only attempt `k` reads the challenge** [PS10, proof of
Proposition 128.8, the reduction to the hiding property] (Claim-129.d): the
```

**E7** (finding 10; **conditional on #210's next round landing `msgAt_eq` and `edgeIdxOfMsg_eq`**).
In `Simulator.lean`, replace the body of `col_zk`

```lean
    ZK (colProtocol Com ℓ) R3COL := by
  sorry
```
by
```lean
    ZK (colProtocol Com ℓ) R3COL :=
  colZK_zk_of_eqs msgAt_eq edgeIdxOfMsg_eq hC
```

If the round publishes implicit binders or another argument order, use
`colZK_zk_of_eqs (fun _ _ => msgAt_eq ..) (fun _ _ => edgeIdxOfMsg_eq ..) hC` (checked).

Sync the docstring of `colZK_planted_eq` (policy §3), which otherwise says the equations "are
not published". Replace its first four lines by

```
/-- **The planted attempt is the hiding view on the planted advice**, conditional on the
equations `msgAt w i = pairFstD (pairSndD^[i] w)` and `edgeIdxOfMsg m w = |w| % m` (published
as `msgAt_eq` and `edgeIdxOfMsg_eq` by PR #210's next round; missing at the fill's base, E-API):
with the endpoint commitments, the planted opening and the later attempts' outcome `post`
hard-wired, `ColZK.hidingView` computes the planted attempt's encoded outcome.
```

A later cleanup, not part of this landing, could drop the `hmsg`/`hidx` hypotheses from the three
private helpers and cite the lemmas directly.

If #210's round has not landed when col-b lands, land E1–E6 only and keep `col_zk` sorried, with
the frontier recorded.

**D1** (findings 4 and 6; ledger, no code). Add to the integration ledger for
`ThreeColoring/{Simulator,ColZKLemmas,ColZKMachine}.lean`:
- the disclosed copy `ColZK.pushesUniform_restrict` (`MultiMessage.pushesUniform_comp_injective`),
  with the cross-unit `dla_pushesUniform_restrict` and the three `pushesUniform_castLE`, as one
  request for a shared `HardcoreBit.pushesUniform_restrict`;
- the near-duplicates of finding 6: `table_index_*` (`finProdFinEquiv`); the `ofFn_*` windows
  (`EnsembleLemmas.take_drop_ofFn_blocks`, `OneWay.ofFn_block_eq_take_drop`);
  `polyTimeComputable_next` (`reply_poly`'s proof); `distAdv_seed_to_coins` (`distAdv_sunglassRed`);
  `field_encodeMsgs` (`ColMachines.getD_eq_pairFstD_iterate`);
- `acceptProb_seed_to_coins` and `findSome?_map_option`, unless E3/E4 land;
- the dependence on `ProtocolProofs.lean`'s `ColProofs.sampleEdgeIdx_ofFn_castLE` and
  `ColProofs.ofFn_getD_lt`;
- the size of `Simulator.lean` (1659 lines): an exception or a split (finding 4).

## Not verified

- The real #210 next-round lemmas: only stubs with the stated statements were checked.
- Landing next to col-a's delivery. col-a owns `Protocol.lean`, where `msgAt_eq` will sit;
  col-b needs only that statement.
- The root `TCSlib.lean`, which is not in the order list.
- The intermediate commits of the series, individually.

## Logs (`$SP/review-colb/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- **Replay and freeze:**
  - `am.log` (empty: clean), `commits.txt`, `diffstat.txt`, `colb.diff` (the reviewed diff);
  - `Simulator.base.lean`, `Simulator.head.lean`;
  - `declfreeze_rev.py`, `declfreeze.log`, `base-order.txt`, `head-order.txt`;
  - `briefstmt.py` (ladder statements against the brief).
- **Elaboration and axioms:**
  - `run-checks.sh` (the driver), `module-checks.log` (the seven head checks);
  - `downstream.py`, `downstream.txt`;
  - `axioms.log` (`probe/Axioms.lean`: prints and the 137-constant sweep).
- **Rule 10:**
  - `probe/Collect.lean`, `collect.log` (the name collection);
  - `probe/Matchers.lean`, `matchers.log`;
  - `seal/mkseal.py`, `seal/names-{ColZKLemmas,ColZKMachine,Simulator}-all.txt`;
  - `seal/RevSealed{ColZKLemmas,ColZKMachine,Simulator}.{lean,out}` and their
    `RevControl*` twins;
  - `seal/RevSealedEval*` (`PolyExpr.eval` sealed too);
  - `seal/RevSealedEdited*` (with E1–E6);
  - `seal/RevSealedFrontierSimulator.{lean,out}` and `RevControlFrontierSimulator.*`;
  - `probe/SimpQ.lean`, `simpq.log`.
- **Lint:** `style-lint-head.log`, `style-lint-edited.log`, `campaign-lint-head.log`,
  `campaign-lint-edited.log`, `prooflen.py`.
- **`edits/`:**
  - the diffs `landing-edits.diff` (E1–E6) and `frontier-edit.diff` (E7);
  - `apply_edits.py`, `apply_frontier.py`;
  - `edited-checks.log`;
  - `frontier-stubs-scratch.diff` (the stubs, scratch only);
  - `frontier-checks.log` (the chain with the stubs), `frontier-checks2.log` (`Simulator` with
    the final E7 text), `frontier-axioms.log` (`probe/AxFrontier.lean`);
  - the edited files `Simulator.landed.lean` (E1–E6), `Simulator.frontier.lean` (E1–E7),
    `ColZKLemmas.edited.lean`, `ThreeColoring.edited.lean`.

The olean copy `$SP/rev-colb-oleans` was deleted after the runs; recreate it from
`$SP/fill-col-b-oleans` to replay. The scratch worktree `$SP/wt-rev-colb` was removed.
