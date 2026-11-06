# Delivery review: fill unit dl-b (the discrete-log hard-core bit)

- **Delivery:** `inbox/fills/dl-b/` on `exchange/pass-shelat-ch5-8` at
  `d442d71ca7d61f5746672e1d81078d84643d38e7` (REPORT.md, 8 patches, `src/`, `evidence/`).
- **Worker branch:** `fill/dl-b`, head `a5c54b0ed4e9aa388bd4497303233d3e044ce419`, base
  `16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1` (the issue commit), 8 commits.
- **Brief:** `brief-issued.md`, unit dl-b (with `review.md`). **Policy:** `policy.md`.
- **Integration partner:** dl-a's landed head `b62c34ee813eeccbaa8a7cbf9964d2356fedbf14` on `fill/dl-a`.
- **Reviewed:** 2026-11-06. This was an independent run:
  - the patches were replayed in a fresh scratch worktree;
  - Lean was re-run one file at a time against a copy of the worker's olean tree, never with
    `lake build`;
  - the seal names were collected from the elaborated terms, not taken from the worker's list;
  - the integration replay was rebuilt in a second scratch copy.

## Verdict: **land after edits**

All seven targets are filled with no `sorry`. The six concrete targets print the standard axioms
at the base. With dl-a's head integrated, all seven do, the headline included. Every base
statement and docstring is byte-identical, and the 210 new declarations are all `private`
`dlb_`. The owned file, the `Candidates` facade and `audits/pass-shelat/Checks` elaborate. The
rule-10 seal holds under this review's own 65-name list, including the compiler-generated matcher
`StateLoop.orbit.match_1`, and each of the six controls closes unsealed and fails sealed. The
headline's four departures from the frozen sketch are sound.

There are **no blockers and no majors**. The edits are minor:
- E1 replaces a private copy of the public `OneWay.statClose_pi` (in the import closure) by a
  citation;
- E2 adds proof sketches to the 12 long private proofs that `scripts/style_lint.py` flags;
- E3 (optional) silences the unused-variable warning of the frozen `hg`, in the proof only;
- E4 refreshes the headline's frozen proof sketch. It needs the maintainer's docstring
  authorization.

Ledger additions are under D1. All edits are proof- or docstring-only. They were checked
unsealed and sealed (see "Landing edits").

## Checks

| # | Check | Result |
|---|---|---|
| 1 | Integrity | Worktree `$SP/wt-rev-dlb` (detached at `16a7d02d`, `.lake/packages` linked); `git am` of the 8 patches is clean (`am.log` empty). The result's tree `74e70561…` is the tree of `a5c54b0e`. The owned file matches `src/` byte for byte (`cmp`), and `src/` holds only that file. `git diff --stat`: 1 file, 2346 insertions, 7 deletions. The 7 removed lines are exactly the 7 `  sorry`. |
| 2 | Statement freeze | Every hunk replaces a target's `sorry` or inserts whole declarations at a declaration boundary (base lines 303, 342, 396, 419, 614 and after the body of `polyTimeComputable_halfStr`). No base statement, definition or docstring changed. All 210 added declarations are `private` with the prefix `dlb_`. No `set_option`, `attribute`, `open`, `sorry` or `native_decide` was added. The added `section … end` pairs and `omit … in` lines enclose only new declarations. The frozen `hg` is finding 4. |
| 3 | Elaboration | `scripts/lean_check_tree.sh`, with `TCSLIB_OLEANS` set to a copy (`$SP/rev-dlb-oleans`), in order. `Candidates/DiscreteLogHardcore` (56 s) has 0 errors and one warning, the unused `hg` at :626. The facade `Candidates` takes 2 s, and `audits/pass-shelat/Checks` takes 127 s with 0 errors. `downstream2.py` gives the owned module and the facade as the only downstream modules: `ElGamal` does not import it. |
| 3 | Axioms | `#print axioms` on the base olean tree (`axioms.log`): the six concrete targets print `[propext, Classical.choice, Quot.sound]`; `fullDLCollection_hardCore` adds `sorryAx`, as do `fullDLCollection_oneWay`, `expCollection_oneWay` and `statClose_sampleBelowL` (dl-a's targets, sorried at the base). |
| 3 | Integration | Second worktree `$SP/wt-rev-dlb-int` at `a5c54b0e`, with `Concrete.lean` and `DiscreteLog.lean` from `b62c34ee`, against a second olean copy. The 26 order-list modules from `Concrete` to `DiscreteLogHardcore` were recompiled in order, all with exit 0 (`integration-replay.log`). Concrete and DiscreteLog have no warnings; DLH has only the `hg` warning. **All seven targets, the headline included, and `fullDLCollection_oneWay`, `expCollection_oneWay` and `statClose_sampleBelowL`, print the standard triple** (`integration-axioms.log`). The worker's claim is reproduced. |
| 4 | Rule 10, own seal | See finding 5. 65 names (`seal/rev-sealed-names.txt`), with `PolyExpr.eval` and its matcher left unsealed (ruling Q1). **The whole-file sealed copy compiles with 0 errors**; its only warning is `hg` (`seal/RevSealedDLH.out`). Controls C1–C6 close unsealed (0 errors) and fail sealed (6 × "Type mismatch"). The grep of 419 rewrite and unfold lists finds no foreign definition used as a rule. |
| 5 | Route | See findings 1–3. |
| 6 | Duplication | See findings 6–7. |
| 7 | Lint | `scripts/style_lint.py` reports 0 findings at the base and 14 at the head: the size line, plus 13 private proofs over 20 lines with no **Proof sketch.** After E1+E2, only the size line remains (`style-lint-*.log`). `campaign_style_lint.py` reproduces the REPORT (8 FAIL, 9 WARN, no FAIL in the owned row). The lint and seal logs below are in `$SP/review-dlb/`. |

## Findings

1. **note: the headline's four departures are sound.** Each one is machine-checked; the question
   is the argument and its necessity.
   - **`T = 2^κ` with `κ = Nat.size (16n^c)`** (instead of `⌈(p−1)/s⌉`). `Nat.lt_size_self` gives
     `16n^c < T`, and `dlb_two_pow_size_le` gives `T ≤ 32n^c`. `dlb_window_params` gives
     `p − 1 < (s+1)·8n^c ≤ 16n^c·s < T·s`, because `s ≥ 2`. The guess is the first `κ` of `n`
     coins, which is exactly uniform (`dlb_guess_pushesUniform`), and `κ ≤ n` because
     `16n^c < 2^n`. The ideal bound is `(3/4)/T ≥ 3/(128n^c)`, half the sketch's `3/(64n^c)`, and
     the final constant is `3/(1024n^{2c})` instead of `3/(512n^{2c})`. That is still an inverse
     polynomial, so the contradiction with `hDL` is unaffected.
     - **Not forced** by any missing interface. It is a sound simplification: it removes the
       second sampled coordinate, the ceiling and the `T < 2^n` guard.
   - **The collection's own domain sampler, with `SampleClose`.** The machine runs
     `S = (fullDLCollection H G).sample` through `S.output`, which equals `S.runAt` because the
     sampler is uniform (`sample_uniform`, `NUPPT.Uniform.runAt_eq`). The coupling in
     `dlb_instance` is correct:
     - the event `P` is read on the *decoded* outputs: every block decodes, and `dlInverter`
       inverts on the decoded coins;
     - on `P` the machine provably outputs `x` (`dlb_raw_sem`);
     - the decoded tuple is `n·ℓ·δ_S`-close to `some` of a uniform tuple (`StatClose.prod`, the
       tuple lemma twice, `abs_uprob_sub_le_prod`);
     - on the ideal side `P` is exactly the inversion event (`expo_injective`).

     `δ_S` is negligible, and the reduction pays `n·ℓ·δ_S(n) ≤ 3/(1024n^{2c})` once `n ≥ 6000`
     and `δ_S(n) < n^{−(4c+3)}`.
     - **Partly forced.** The REPORT says that no published lemma states `expSampleRaw`'s
       equation. That is imprecise: `expSampler_runAt` (`DiscreteLog.lean:540`) is published at
       the base, and it is exactly the sampler's run equation through `sampleBelowL`. What is
       missing is the coin count, `(expSampler H).coins = .mul .var .var` (it holds by
       `NUPPT.coins_ofPolyTimeUniform` only after unfolding `expSampler`). Without it the trial
       blocks cannot be identified with `Fin (n·n) → Bool` for `statClose_sampleBelowL`.
     - `expSampler_coins` belongs in `Candidates/DiscreteLog.lean`, beside `expSampler`.
       `expSampleRaw_eq` is not needed, since `expSampler_runAt` already covers it.
     - Publishing `expSampler_coins` would **not** simplify this proof enough to matter. The
       collection-sampler route is shorter than the sketch's, because it needs no
       `statClose_sampleBelowL` and no decode composition. It also keeps the machine free of a
       third rejection loop (policy §2, "no third private variant"). Keep it.
     - The `SampleClose` is taken from `(fullDLCollection_oneWay H G hDL).sampleClose`. That
       makes the hard part depend on dl-a's deepest target. `expCollection_sampleClose` (no
       `hDL`), read through the own-file `fullDLCollection`, would suffice. This is optional and
       not proposed as an edit, because both are filled and axiom-clean after integration.
   - **`ℓ = 16n^{2c+1} + 1` (odd).** `n/(ε'²ℓ) = 4nX²/(16nX² + 1) < 1/4` with `X = n^c`
     (`dlb_arith_success`).
     - **Forced.** `HardcoreBit.majority` (`HardcoreBit/PairwiseIndependence.lean:235`) has no
       defining equation. The published `two_mul_card_le_of_majority_ne` pins it down only when
       ties are impossible (`dlb_majority_eq_of_odd`). The machine's majority is the string test
       `|w| < 2·count true` (`polyTimeComputable_majority`). The missing lemma
       `HardcoreBit.majority_eq` belongs beside `majority` in `PairwiseIndependence.lean`.
     - With it, `ℓ` could be the sketch's even `16n^{2c+1}`. That would remove
       `dlb_majority_eq_of_odd` (16 lines with its docstring) and the `hodd` threading through `dlb_oStep_round`,
       `dlb_loop_sem`, `dlb_raw_sem` and `dlb_instance`. That is a modest simplification, not
       worth reworking the proof for. Request the lemma for the next shared-file window.
   - **No guard, and advice `⟨A.advice n, ⟨⟦8n^c⟧_n, 1^κ⟩⟩`.** The loops have fixed lengths from
     the unary counters `1^n` and `1^ℓ`, with `1^ℓ = unaryPoly ℓP` of `1^n`. So polynomial time
     holds on every input (`dlb_raw_poly`, through the public `StateLoop.gstep` host), and the
     analysis bounds success below by `0` off the good set. The sketch's guard protected the
     `T`-sampler, which no longer exists.
     - The unary `1^κ` in the advice is legitimate for a non-uniform PPT: its length is bounded
       by `dlb_advP` (`dlb_advice_length`). It could also be computed from `⟦8n^c⟧_n` with
       `H.add` and `H.size`; the advice is simpler.
     - **Not forced.** Both are consequences of `T = 2^κ`.

2. **minor: the frozen sketch of `fullDLCollection_hardCore` no longer describes the proof.** It
   names:
   - `T = ⌈(p−1)/s⌉` and `K(n) = 16n^c`;
   - `ℓ = 16n^{2c+1}`;
   - the guard;
   - the coins `n·n + n·ℓ·(n·n + A.coins)`;
   - two `sampleBelowL` samplers, through `polyTimeComputable_iterateFind`;
   - `polyTimeComputable_iterateEmit` and `NUPPT.polyTimeComputable_layout`;
   - the loss `(1 + 16n^{2c+2})(1/2)^n`;
   - the constant `3/(256n^{2c})`.

   None of these is in the proof. Policy §3 ("Synchronization") requires the sketch to follow the
   proof, but the brief freezes docstrings, so the REPORT's §1.1 disclosure was correct
   behaviour. **E4** is the exact refresh. It replaces only the `**Proof sketch.**` paragraph and
   changes no statement. It needs the maintainer's docstring authorization. If E4 is not
   authorized, keep REPORT §1.1 as the record ("sketch refresh owed").

3. **nit: two other frozen sketches cite lemmas the proofs do not use.** Both are still true at
   the level they describe. No edit is proposed; refresh them at the next docstring window if
   wanted.
   - In `polyTimeComputable_halfStr`, the negation is `polyTimeComputable_not` on
     `polyTimeComputable_headD`, not `polyTimeComputable_ite` on `polyTimeComputable_pairEq`.
   - In `invProb_shiftInverter_ge`, the per-section product is `HardcoreBit.uprob_prod_and`
     with `OneWay.uprob_eq_one_div_card` and `HardcoreBit.uexp_mono`; `pushesUniform_fst` is
     not used.

   The other four target sketches (`dlBits_pow`, `uprob_trial_ge`, `uprob_majOracle_ne_le`,
   `invProb_dlInverter_ge`) match their proofs. In `uprob_trial_ge` the bijection is
   `Equiv.addLeft` through `uprob_comp_equiv`, which is the sketch's `r ↦ e + r`.

4. **note: the frozen `hg` of `invProb_shiftInverter_ge` is redundant, not vacuous, and the
   statement is the intended one.** The proof never needs `hg`:
   - `invProb (expo g) B` asks for `expo g (B (expo g x)) = expo g x`;
   - on the event "`t = ⌊x/s⌋` and `B₀` succeeds", the shifted output is `x` itself
     (`dlb_shiftInverter_eq`), so the bound holds for every `g ∈ Z_p^*`.

   `hg` is satisfiable, and the only consumer (`invProb_dlInverter_ge`) has it anyway. It is a
   harmless hypothesis kept for uniformity with the concrete layer, and gate 03f1 (row 69)
   screened the statement as true. Dropping it would be a generalization, that is, a statement
   change for a statement window; it is not needed. **E3** (optional) silences the linter
   warning inside the proof with `have _ := hg` and a comment. `clear hg` does not silence it
   (probe `probe/Unused.lean`).

5. **note: rule 10 holds under this review's seal; the worker's seal and its fixes are
   confirmed.**
   - **Collection** (`probe/Collect.lean`, `collect.log`). Over the 408 constants of the 7
     targets and the `dlb_` family (auxiliaries included), this review collected the
     other-module, non-reducible, non-instance TCSlib definitions in the elaborated types and
     values: 58 names (narrow pass).
   - The wide pass adds the statements of every constant used and, transitively, the bodies of
     the own-file definitions used. That gives 63 names: `ExpGroupGen.DLHard`, `expCollection`,
     `expCollection_coinsEquiv`, `expCollection_domEquiv` and `NUPPT.Uniform` are added.
   - The compiler-generated matchers of those definitions are `StateLoop.orbit.match_1` and
     `PolyExpr.eval.match_1`. None of the definitions is `@[simp]`.
   - **Seal:** the union with the worker's 63 names, minus `PolyExpr.eval` and its matcher
     (ruling Q1). That is 65 names, with `orbit.match_1` included.
   - **Differences from the worker's list.** The worker sealed `PolyExpr.eval`, which is stricter
     than required. The worker did not list `expCollection_domEquiv`, `expCollection_coinsEquiv`
     or `orbit.match_1`, and this review's collection does not find the worker's `expDec` or
     `NUPPT.coinsEquivPoly`. Both are sealed here anyway.
   - **Result:** the whole-file sealed copy compiles. The base's non-target proofs in this file
     also pass sealed.
   - **Controls** (`seal/RevControl{Unsealed,Sealed}.lean`), each closing unsealed and failing
     sealed:
     - C1: `dlP` by its body;
     - C2: `StateLoop.orbit … 0` by `rfl`;
     - C3: `A.coinLen n = A.coins.eval n` by `rfl`;
     - C4: `HardcoreBit.majority` by its body;
     - C5: `StateLoop.orbit.match_1` against an own-file matcher on the same discriminant;
     - C6: `StatClose` by its body.

     A matcher seal blocks only lazy-delta reads: iota reduction of a matcher on a constructor
     is not blocked. C5 shows that the seal is active.
   - **Grep** (`tools/grepforeign.py`, `grep-foreign.txt`): 419 `simp`/`simp only`/`rw`/`rwa`/
     `simp_rw`/`dsimp`/`unfold`/`delta` lists in the added code. No foreign definition is used as
     a rule. The one lexical hit is `pairSndD` as the `start` argument of
     `StateLoop.gstep_iterate_eq`. Every `unfold` names an own-file definition. The 86 bare
     `simp` calls cannot unfold a foreign definition, because none is `@[simp]`.
   - **The worker's seal fixes are confirmed** (commit `a5c54b0e`):
     - `PolyExpr.var.eval` and `id` in `dlb_stateIterate_poly`;
     - `orbit … 0` by `rfl` in `dlb_orbit_eq`;
     - `StatClose` by `intro` in `dlb_statClose_pi`, which E1 deletes;
     - `Collection.SampleClose` applied as a function;
     - `Negligible` applied as a function. That is **four** sites, not the REPORT's "three":
       `negligible_two_pow_neg`, `hδ`, `hδS` and `hDL B`.
   - **Remaining readings: none.** No published lemma is needed beyond those the brief lists. The
     only missing interfaces are the two equations of finding 1, and both are used around, not
     read.

6. **minor: `dlb_statClose_pi` is an undisclosed copy of a public lemma in the closure.** The
   REPORT calls it "new: … promote to `Asymptotic/Sampling.lean` as `StatClose.pi`". It is
   `TCSlib.Cryptography.OneWay.statClose_pi` (`Asymptotic/OneWayLemmas.lean:278`):
   - that module is in this unit's order list (line 63) and in the file's import closure;
   - the statement is identical up to binder names;
   - the proof is the same, by induction, `StatClose.prod`, `StatClose.map Fin.cons` and
     `Fin.consEquiv` on both sides.

   Two more copies exist outside the closure, `GIZK.statClose_pi` and `GI.statClose_pi`. It is
   not a Mathlib lemma, because `StatClose` is TCSlib's. **E1** deletes the 36-line copy and
   cites `OneWay.statClose_pi` at its one use (`dlb_instance`, twice). The file then compiles
   unsealed and sealed. The promotion request is withdrawn; a move of `OneWay.statClose_pi` to
   `Sampling.lean` is a separate shared-file question.

7. **minor: the reuse screen is otherwise confirmed, with additions (D1).** The disclosed rows
   are confirmed:
   - `dlb_stateIterate_poly`: the 8-line body of `polyTimeComputable_stateIterate` (`HardCoreLoops`,
     outside the closure) at `out = pairSndD`. Moving it into `Complexity.StateLoop` is
     endorsed.
   - `dlb_count_ofFn`: verbatim the proof of `count_true_ofFn` (`HardCoreGL`, outside).
   - `dlb_foldl_bits` and `dlb_listToNat_cons`: the private `foldl_bits_eq` (`Sampling`) and
     dl-a's `dla_listToNat_append`.
   - `dlb_two_pow_size_le`: related to `two_pow_size_le` (`HardCoreGL`, `≤ 2x + 1`).
   - The applied-form wrappers: `dlb_ptc` is the private `ptc_comp` of `Randomized/Closure.lean`.
   - The modular-numeral layer.

   The promotion requests (`StateLoop` stateIterate, `listToNat_cons`/`listToNat_append`, an
   applied `PolyTimeComputable.comp'`, a shared modular-numeral layer) are endorsed, as is the
   proposed post-fill split.

   **Not disclosed:**
   - `List.count_ofFn` (`TCSlib/Programs/Util/List.lean:396`, general `α`, outside the closure)
     is a third copy of `dlb_count_ofFn`. Mathlib has none.
   - The bound `2^{size m} ≤ 2m` of `dlb_two_pow_size_le` is also proved inline as `hk2` in
     dl-a's landed `statClose_sampleBelowL` (`DiscreteLog.lean`, `b62c34ee`, :616) and as `h2` in
     `statClose_sampleEdgeIdx` (`ThreeColoring/Language.lean:398`). The latter takes three lines
     from Mathlib's `Nat.lt_size` and is the shortest form. A shared `Nat.two_pow_size_le_two_mul`
     would serve all three. Mathlib has `Nat.size_le`, `Nat.lt_size` and `Nat.lt_size_self`, but
     not this bound.
   - `dlb_cut` with `dlb_guess_pushesUniform` is the `e`-equivalence argument of the three
     `pushesUniform_castLE` copies (`GraphIsomorphismZK/Closeness.lean:105`,
     `ThreeColoring/ProtocolProofs.lean:352`, `GraphIsomorphism/Proofs.lean:584`, all outside the
     closure), in addition to the REPORT's `dla_pushesUniform_restrict` and
     `pushesUniform_comp_injective`. dl-a's `HardcoreBit.pushesUniform_restrict` request would
     cover all of them.

   No number-theoretic fact is re-proved: Euler's criterion, `pow_mod_orderOf`,
   `Nat.card_zpowers` and the `ZMod` value lemmas are all Mathlib's. `dlb_isGenerator` uses
   `Subgroup.eq_top_of_card_eq` with `Nat.card_zpowers`. Mathlib's converse direction is
   `orderOf_eq_card_of_forall_mem_zpowers`, and no direct "order = card ⇒ generator" lemma for
   `IsGenerator` exists.

8. **minor: 12 long private proofs have no proof sketch** (policy §3, checklist 4;
   `style_lint.py`). The 12 are:
   - `dlb_inner_eq`, `dlb_oStep_cons`, `dlb_oStep_shape`, `dlb_outer_eq`;
   - `dlb_qrF_eq`, `dlb_rootF_eq`, `dlb_vote_eq`, `dlb_oStep_round`;
   - `dlb_loop_sem`, `dlb_raw_sem` (123 lines);
   - `dlb_instance` (132 lines), `dlb_reduction` (140 lines).

   The thirteenth flagged proof is `dlb_statClose_pi`, which E1 deletes. The worker ran only
   `campaign_style_lint.py`, which skips private declarations. **E2** appends a
   `**Proof sketch.**` paragraph to each existing docstring. Afterwards `style_lint.py` reports
   only the size line.

9. **nit: REPORT accuracy.** Besides findings 5 (four `Negligible` sites, not three), 6
   (`dlb_statClose_pi` is not new) and 1 (`expSampler_runAt` is published), the REPORT is
   accurate:
   - the target routes;
   - the 210 private declarations and their roles;
   - no re-points needed (`halfStr_spec` and `halfPred_eq` were already in the brief's form at
     the base, confirmed);
   - no E-API;
   - the name corrections;
   - the two elaboration notes;
   - the sweep census (71 in 14 modules; this review's downstream checks agree for the owned
     module);
   - the axiom prints;
   - the lint line.

   The sweep log was taken at `ff22c944`, one commit before the head. This review re-checked the
   owned file and its downstream at the head.

10. **nit: docstrings of private helpers.** 99 of the 210 private declarations have no docstring
    of their own. Most are projections (`dlb_fu` …, `dlb_zy` …) and `_poly`/`_natToList`
    companions that sit under a group docstring. Policy §2 leaves private docstrings to the
    reviewer's discretion, and the group docstrings suffice. Five substantive ones would benefit
    from one line at the next touch: `dlb_vote_dec`, `dlb_ofFn_split`, `dlb_split_bijective`,
    `dlb_B_runAt` and `dlb_B_coinLen`. This is not a landing condition.

11. **note: file size.** The file is 3036 lines, up from 697 at the base, and 3091 with E1–E4.
    The standing user rule allows a fill-owned file past 1000 lines with no split. The worker's
    proposed split, the machine and reduction as `Candidates/DiscreteLogHardcoreMachine.lean`
    and the modular numerals beside `Arithmetic.lean`, is recorded for the next shared-file
    window. Noted only.

## Landing edits (exact)

All diffs are under `$SP/review-dlb/edits/`:
- `landing-edits.diff` holds E1–E4 and applies with `git apply --check` (clean on the head);
- `landing-edits-E1-E3.diff` holds the code and private-docstring edits only;
- `landing-edits-E4-docrefresh.diff` holds E4 on top of them.

The generators are `apply_edits.py` (E1–E3) and `apply_docrefresh.py` (E4). Every diff touches
only `TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean`, and none changes a statement.

The edits were checked to elaborate:
- E1–E3 (`edits/DLHEdited.lean`): 0 errors, 0 warnings;
- E1–E4 (`edits/DLHEdited2.lean`): 0 errors, 0 warnings;
- the sealed copy of E1–E4 (`edits/DLHEdited2Sealed.lean`, the same 65 names): 0 errors,
  0 warnings. Its axiom prints are standard for the six concrete targets, and the headline
  carries only dl-a's base `sorryAx`.

The edits are proof- and docstring-only, so the downstream modules, which read statements only,
are unaffected.

**E1** (finding 6). Replace the section header and the whole of `dlb_statClose_pi`, from
`/-! ### Closeness of independent coordinates; the guess -/` up to, but not including,
``/-- Splitting an `n`-bit string at `κ ≤ n` ``, by

```
/-! ### The guess -/

```

and in `dlb_instance` replace

```lean
  have hXn := dlb_statClose_pi (dlb_statClose_pi hX1 ℓ) n
```
by
```lean
  have hXn := OneWay.statClose_pi (OneWay.statClose_pi hX1 ℓ) n
```

**E2** (finding 8). Append a `**Proof sketch.**` paragraph to the docstrings of the 12 helpers
listed in finding 8. The exact text is in `landing-edits-E1-E3.diff`. For example, for
`dlb_raw_sem`:

```
**Proof sketch.** Read the layout (`NUPPT.inParam_layout`, `inArg_layout`,
`inAdvice_layout`, `inCoins_layout`): `p` and `g` from the index, `⟦D⟧_n` and `1^κ` from the
advice, the guess block and the round coins from the coins. Each bundle operation is evaluated on
numerals (`subStr_pairEncode`, `dlb_quot_natToList`, `mulStr_pairEncode`,
`dlb_powMod_natToList`, `dlb_invMod_natToList`, `dlb_mulMod_natToList`): `s = ⌊(p − 1)/D⌋`,
`ts = t · s`, `y₀ = y · (g^{ts})⁻¹`, and the fixed data hold `g⁻¹`, `(p − 1)/2`, `p/4 + 1`, the
unary coin lengths and `1^ℓ` (`dlb_fix_proj`). The round loop runs exactly `n` rounds
(`dlb_outer_eq`) and its bits read `dlLoop g (majOracle g A_i ℓ) n y₀ c` (`dlb_loop_sem`); the
output `(bits + ts) mod (p − 1)` (`addStr_pairEncode`, `dlb_rem_natToList`) is the value of
`shiftInverter` (`ZMod.val_natCast`). -/
```

**E3** (finding 4; optional). In the proof of `invProb_shiftInverter_ge`, after `classical`,
insert

```lean
  -- the bound holds for every `g`; the frozen statement keeps `hg`, which the proof does not need
  have _ := hg
```

**E4** (finding 2; **needs docstring authorization**). In the docstring of
`fullDLCollection_hardCore`, replace the paragraph from
``**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`,``
to the end of the docstring (``contradicting `hDL B` via `not_negligible_iff`. -/``) by the text
in `landing-edits-E4-docrefresh.diff`. It covers:
- *Easy*: unchanged;
- *Hard*: `ε(n) = max(succ(n) − 1/2, 0)`, then `good_instances` with `2ε'` and the `hbig`
  removal, and the transport to `predProb (expo g_u) (halfBit (p−1)) A_i`;
- `invProb_dlInverter_ge` with `ε'`, `s = ⌊(p−1)/(8n^c)⌋`, `T = 2^κ` (`16n^c < T ≤ 32n^c`),
  `k = n` and the odd `ℓ = 16n^{2c+1} + 1`;
- the machine: advice `⟨A.advice n, ⟨⟦8n^c⟧_n, 1^κ⟩⟩`, coins `n + n·ℓ·(S.coins + A.coins)`, the
  guarded state loops with unary counters and no guard, and the trial, majority and output
  steps;
- sampling through the collection's `SampleClose` and `OneWay.statClose_pi`;
- the conclusion `G.dlProb B n ≥ (ε'/2)(3/(128n^c) − n·ℓ·δ_S(n)) ≥ 3/(1024n^{2c})`.

The statement is untouched. If E4 is not authorized, land E1–E3 alone
(`landing-edits-E1-E3.diff`).

**D1** (finding 7; ledger, no code). Add these entries to the integration ledger for
`DiscreteLogHardcore.lean`:
- the copies `dlb_stateIterate_poly` (of `polyTimeComputable_stateIterate`) and `dlb_count_ofFn`
  (of `count_true_ofFn`; also `List.count_ofFn`, `Programs/Util/List.lean`);
- `dlb_foldl_bits` and `dlb_listToNat_cons` (`foldl_bits_eq`, `dla_listToNat_append`);
- the `2^{size m} ≤ 2m` family (`dlb_two_pow_size_le`; dl-a's inline `hk2`; 3-colouring's
  inline `h2`; `two_pow_size_le` and `two_pow_size_le_two_mul_succ` in the `+1` form);
- `dlb_cut`/`dlb_guess_pushesUniform` (the `pushesUniform_castLE` triple,
  `dla_pushesUniform_restrict`, `pushesUniform_comp_injective`);
- the `statClose_pi` family outside the closure (`GIZK.statClose_pi`, `GI.statClose_pi`), unless
  E1 lands, in which case `dlb_statClose_pi` is gone;
- the interface requests `HardcoreBit.majority_eq` (`HardcoreBit/PairwiseIndependence.lean`) and
  `expSampler_coins` (`Candidates/DiscreteLog.lean`). `expSampleRaw_eq` is not needed: the
  published `expSampler_runAt` covers it.

## Not verified

- The full 94-module sweep was not rerun. This review checked the owned module, its downstream
  (the facade and `Checks`) at the head, and the 26-module integration chain.
- The 86 bare `simp` calls were not run through `simp?`. No foreign definition is
  `@[simp]`-unfoldable (collector, `simpUnfold=false` for all), so they cannot read one.

## Logs (`$SP/review-dlb/`, `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`)

- `deliv/`: the exported delivery, from `git archive` of `d442d71c`.
- `am.log` (empty: the replay is clean) and `dlb.diff` (the reviewed diff, base to head).
  `base.lean` is the owned file at the base.
- `run-checks.sh` (driver) and `module-checks.log` (owned file, facade, `Checks`, with times).
- `axioms.log`: the base-tree axiom prints. `integ-order.txt`, `integration-replay.log` and
  `integration-axioms.log`: the integration replay.
- `probe/`:
  - `run1.sh` (probe runner);
  - `Axioms.lean`;
  - `Collect.lean` (the seal-name collector) with `collect.log`, `seal-rows.txt`, `narrow.txt`,
    `wide.txt`, `wide-only.txt`, `worker.txt` and `full-names-collected.txt`;
  - `Unused.lean` (the linter probe for E3).
- `seal/`:
  - `rev-sealed-names.txt` (65 names) and `mkseal.py`;
  - `RevSealedDLH.lean` and `.out` (the whole-file sealed copy, 0 errors);
  - `RevControl{Unsealed,Sealed}.lean` and `.out` (C1–C6);
  - `MatchProbe.lean` (the matcher signature).
- `tools/grepforeign.py` and `grep-foreign.txt`.
- `style-lint-{base,head,edited}.log` and `campaign-lint-{head,edited}.log`.
- `edits/`:
  - `landing-edits.diff`, `landing-edits-E1-E3.diff` and `landing-edits-E4-docrefresh.diff`;
  - the generators `apply_edits.py` and `apply_docrefresh.py`;
  - `DLHEdited{,2,2Sealed}.lean` with their `.out`.

The scratch worktrees `$SP/wt-rev-dlb` and `$SP/wt-rev-dlb-int` and the olean copies
`$SP/rev-dlb-oleans` and `$SP/rev-dlb-int-oleans` were removed after the runs. To replay,
recreate them from `$SP/fill-dl-b-oleans`. The exchange checkout `$SP/wt-exchange` was only
fetched; its branch did not move.
