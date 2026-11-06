# Library re-derivation sweep of `Hierarchy.lean`

Target: `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean` at the landing branch `lean/b6h-landing`
(worktree `wt-h`, head `14ee2e46`, "Merge B6's H fill delivery"). The file has 2,563 lines and
43 private declarations, all `sph_`/`sph…`. All line numbers below are lines of that source. It is
copied here as `Hierarchy.src.lean` (`cmp`-identical to the worktree file and to `git show`).

Method: the G5 sweep's (`agents/g5sweep/README.md`), followed step for step. Copy A runs `exact?`
in place. File B runs generalised `example`s. B2 runs name checks, term checks and `apply?`. Then
one tested replacement copy C.

Nothing tracked was edited, committed or pushed. `git status --short` is empty in `wt-h` and
`wt-hk`. In `/home/user/tcslib` it shows only one untracked file,
`campaign/items/dedup/as1-SCOPE.md`, which this sweep did not create. Scratch Lean files are in `wt-hk/rvprobe/hsweep/`, which is git-excluded
through `rvprobe/`.

Lean was run only as
`bash /home/user/tcslib/devtools/seyoon/leanelab.sh /home/user/tcslib-scratch/wt-hk /home/user/tcslib-scratch/oleans-lnth rvprobe/hsweep/<File>.lean`.
Each command was prefixed by `. /home/user/tcslib-scratch/env.sh`. Elaborations ran one at a time,
and Python only as `python3 -I`. Each log ends with `-- exit=N, T s (snapshot oleans-lnth)`. Every
probe copy, and every replacement copy, replaces the file-level `set_option maxHeartbeats 0` by
`400000`. Every `exact?`/`apply?` also carries `set_option maxHeartbeats 400000 in`. The
unmodified file elaborates under 400000 (`base4.log`), so no proof needs the unbounded setting.

## Result

| class | items | sites |
|---|---|---|
| clear hits | **G1–G9, K1** | 20 |
| borderline (M class) | **M1–M8** | 15 |
| needs an import | none | 0 |
| optional cosmetic | O1–O8 | 8 |

* **Clear hits: G1–G9 and K1 (10 items, 20 sites).** K1 is a field-by-field `Cfg.ext` skeleton
  that re-proves two published TCSlib lemmas.
* **Borderline: M1–M8 (8 items, 15 sites).**
* **Needs an import: none.** Every replacement lemma is in the file's import closure (106 TCSlib
  modules, `closure.txt`). Unlike G5's closure, this one has `smul_eq_mul`, `Fin.sum_const` and
  `Finset.card_fin`.
* **Optional cosmetic: O1–O8.** These are not hits.

`copyC.diff` applies G, K and M together (27 hunks, +41 −80; the file goes from 2,563 to 2,524
lines). **Copy C elaborates with exit 0, and its only messages are the two expected `sorry`
warnings**: `space_universal` at 147:8 (F6's) and `SPACE_linear_ne_NP` at 2521:8. This matches the
unmodified baseline, which has the same two warnings at 147:8 and 2560:8.

Two variants also elaborate with exit 0 and only those two warnings:

* **copy CG** (`copyCG.diff`, 17 hunks, +24 −62): clear hits only, G1–G9 and K1, without the M
  items;
* **copy D** (`copyD.diff`, 34 hunks, +51 −107): copy C plus O1–O8.

All three diffs are against the target path (`a/…`, `b/…`). Each one applies with `patch -p1` to
`git show 14ee2e46:<path>` and reproduces the tested copy byte for byte. `git apply --check` also
passes on `wt-h`. None touches line 16 (`maxHeartbeats 0`). Every hunk keeps its
`have`/`lemma`/`def` statement unchanged, so the hunks are independent. No added line is over 100
characters.

| id | line(s) | declaration: step | inline proof | published lemma (replacement) |
|---|---|---|---|---|
| **G1** | 177–179 | `sph_inclusion`: second `by_cases` branch | `calc … _ = (F+1)*1 := (Nat.mul_one _).symm; _ ≤ (F+1)*g n := Nat.mul_le_mul_left _ (hfloor n)` | `_ ≤ (F + 1) * g n := Nat.le_mul_of_pos_right _ (hfloor n)` (core). Its proof is the same two steps. |
| **G2** | 1027, 1042 | `sph_runner_run`: `hz`, `0 < i.val` | `fun h => hi (Fin.ext h)` (×2) | `Fin.val_ne_zero_iff.mpr hi`. Same class as G5's G5 (`Fin.val_ne_of_ne`). |
| **G3** | 1775–1777, 1790–1792, 1793–1795 | `sph_record_suffix`: `(0 : Fin (KI+KR+m+2)) ≠ 1` (×3) | `intro h; have hh := congrArg Fin.val h; rw [Fin.val_zero, Fin.val_one] at hh; omega` | `Fin.zero_ne_one` |
| **G4** | 1865 | `sph_record_size`: `hk : k ≤ k * g n` | `simpa only [mul_one] using Nat.mul_le_mul_left k hfloor` | `Nat.le_mul_of_pos_right k hfloor` |
| **G5** | 1854, 2048 | `sph_record_size` `hb`, `sph_valid_machine` `hbits`: `m.bits.length ≤ m` | `LogProg.length_bits_le Nat.lt_two_pow_self` (×2) | `length_bits_le_self _` (`Turing.`, `Encoding.lean:290`). See the note below. |
| **G6** | 2332–2333 | `sph_diagonal_language` `hind`: `bit = answer …` from `htest` | `cases hb : bit <;> cases ha : … <;> simp_all only […]` (a 4-way case bash) | `exact Bool.eq_iff_iff.mpr htest.symm` (= `Bool.coe_iff_coe.mp`) |
| **G7** | 621–623 | private `sphEmptySel : Fin 0 ↪ Fin k` | `toFun := Fin.elim0; inj' := fun i => Fin.elim0 i` | `Function.Embedding.ofIsEmpty` (`⟨isEmptyElim, isEmptyElim⟩`). The name is kept, so its 8 uses are untouched. |
| **G8** | 560–589 | `sph_radius_run`: space bound, `∑ j ≤ (KI+KR+M.k+2) * r` | `apply Finset.sum_le_sum` to a constant sum, then `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; rfl` | `apply Finset.sum_le_card_nsmul` (the per-tape body is unchanged), then `rw [Finset.card_fin, smul_eq_mul]`. Same pattern as G5's G4 + K1. |
| **G9** | 863–866 | private `sphInitSel : Fin (KI+2) ↪ Fin (KI+KR+m+2)` | `toFun i := ⟨i.val, _⟩`, injectivity by `Fin.ext ∘ congrArg val` | `Fin.castLEEmb (by omega)`. Mathlib's definition is `toFun := castLE h`, which is `⟨i.val, _⟩`. The name is kept, and `h0`/`h1 := Fin.ext rfl` still hold. |
| **K1** | 1252–1260, 1610–1618, 1668–1676, 1756–1761 | `sph_verdict_run` `hp`; `sph_suffix` `hstart`, `hmaps`; `sph_record_suffix` `hstart` | `apply Cfg.ext` plus five field rewrites through two or three `mapState` layers. The goal is `c.mapState F = c` (or `= c.mapState G`). | `simp only [_, Cfg.mapState_mapState]`, then `exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl`, or `rfl` for `hmaps`. The lemmas are `InputRewind.lean:49` and `CfgFacts.lean:69`. Both proofs are this skeleton verbatim. The file already uses `rw [Cfg.mapState_mapState]; rfl` at 1959 and 1994. |
| M1 | 342, 1180 | `sph_right_run`; `sphEmitContract.cut` | `have : u = 0 := by omega` (from `hu : u < 1`) | `Nat.lt_one_iff.mp hu` |
| M2 | 347, 384 | `sph_right_run`; `sph_emit_run` | `have : u = 0 ∨ u = 1 := by omega` | `Nat.le_one_iff_eq_zero_or_eq_one.mp hu` |
| M3 | 616, 2136 | `sph_radius_run` `hn`; `sph_validated_machine` `hrad` | `(0 : ℤ) ≤ ↑n := by omega` | `Int.natCast_nonneg _` |
| M4 | 462–464 | `sphWitnessSel.inj'` | `omega` from `h' : a + i = a + j` | `exact Nat.add_left_cancel h'` |
| M5 | 168–169, 234–235, 1853, 2049, 2346 | five floors `1 ≤ g n` from `logSpace n ≤ g n` | `rw [logSpace_eq] (at h); omega`, inside `le_trans` at 168/234 | `Nat.one_le_of_lt h`. This is definitional: `logSpace_eq` is `rfl`, so `logSpace n ≤ g n` is `Nat.log 2 n < g n`. No published `1 ≤ logSpace n` lemma exists. |
| M6 | 1349 | `sph_seam_avoids` `obtain` | `⟨u - (t + 1), by omega⟩` | `Nat.exists_eq_add_of_le (Nat.lt_of_not_le h)`. Same class as G5's M3. |
| M7 | 1823–1825 | `sph_record_suffix` `hSB` | `(Nat.mul_le_mul_left _ (by omega)).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))` | `Nat.mul_le_mul (Nat.le_add_left _ _) (by omega)`. Its proof is this `trans`. |
| M8 | 1351–1353 | `sph_seam_avoids`: right segment | `cases hq : … with \| none => … \| some q => …` | `obtain ⟨_, _, hq⟩ := Option.map_eq_some_iff.mp hbad; exact Sum.inr_ne_inl hq`. Two lemmas, as in G5's G8. It is ranked borderline because no single lemma states the fact (B34 ✗). |

**Taking only part of the result.** The maintainer can take the clear hits alone, which means
copy CG's diff. That copy also elaborates cleanly.

**Note on G5.** By the G5 taxonomy, two chained citations that make one lemma are M class. I
counted G5 as clear anyway, for three reasons:

* the lemma is TCSlib-published;
* the module's own `space_universal` docstring cites it (line 141, `Turing.length_bits_le_self`);
* the H review's M2 and the reworked brief bind it among the readings to name.

Demote it to M if strict consistency with G5's M1 is preferred.

**Note on M5.** M5 depends on unfolding `logSpace` definitionally. It is accepted, as copy C
shows, but it relies on a definitional fact. A maintainer who prefers the published equation can
keep the five sites, or write `Nat.one_le_of_lt (logSpace_eq n ▸ h)`.

## Optional (copy D = copy C + these; not hits)

| id | line | change | why optional |
|---|---|---|---|
| O1 | 1268 | `ht : t + 2 = t + 1 + 1 := by omega` → `rfl` | definitional (A20 `exact rfl`) |
| O2 | 2159–2164 | `hstart₁` `Cfg.ext` skeleton → `rfl` | definitional through `Cfg.init`/`Cfg.mapState` (A36 `exact rfl`). The field args of `mapState_eq_of_fields` would not be `rfl` here without unfolding. |
| O3 | 2216–2221 | `hpre` `Cfg.ext` skeleton → `rfl` | same (A39 `exact rfl`) |
| O4 | 538–540 | `hout'`: `List.map_congr_left … RecSym.digitEmb_apply` → `rfl` | definitional (A11 `exact rfl`). `digitEmb_apply` is the published reading, so keep it under the "readings, not unfolding" discipline. |
| O5 | 921 | `(by have := j.isLt; exact this)` → `j.isLt` | cosmetic. The goal is `(ι j).val < KI + 2` by defeq, so A15 `exact?` ✗. |
| O6 | 220–221 | `hx`: residual `omega` after `simp only` → `exact Nat.le_add_left _ _` | residual-goal `omega` (idiom class; A04 found it) |
| O7 | 335–340 | positive endpoint of the right move: `by_cases` over two published moves → `LogProg.moveInputPos_val` + `simp only [Fin.eta]` + `omega` | an alternative route through the published clamp formula, not a re-derivation of one lemma (A07/B11 ✗, `apply?` none) |
| O8 | 1096–1098 | private `sphRecordSel : Fin 1 ↪ Fin (k+1)` → `Fin.castLEEmb (by omega)` | agrees with `toFun _ := 0` only extensionally (`Fin 1` is a singleton). `h0 : ι 0 = 0 := rfl` still holds. |

## Method

1. **Enumeration.** I read the whole file.
   * `all_sites.txt` (from `grep -nE`, 769 lines) lists every `have`/`obtain` (289), private
     declaration (43), `calc` step, anonymous `have :=`, and `rw`/`simp only`/`simpa only`/`omega`/
     `nlinarith` line.
   * For TCSlib facts I computed the import closure (`closure.py` → `closure.txt`, 106 modules)
     and searched it at `14ee2e46` with `git grep`. I searched for:
     * a `1 ≤ logSpace` floor (none; only `logSpace_le_succ`, `_mono`, `_le_size_succ`, `_le_of_le_mul_two_pow`);
     * `length_bits_le_self` (found);
     * every `mapState` declaration (`Cfg.mapState_mapState`, `Cfg.mapState_eq_of_fields`, `_const_eq_mapState_sigma`, `_sigma_state_ne`);
     * `moveInputPos_*` (`LogProg.moveInputPos_val` found);
     * the `PSPACE` inclusions (`space_poly_subset_PSPACE`, `SPACE_succ_pow_subset_PSPACE`);
     * the `pairEncode` lemmas;
     * the `SPACE` monotonicity lemmas;
     * the seam, select, emitter, contract, record and window names.
   * The published one-step emitters are `Bool`-only: `Turing.FinTM.emit_run`, `emitCfg`, `rightCfg_run`.
   * `framedContract` exits at `some done`, not at the halt, so it does not cover `sphEmitContract`.
   * No `Cfg.select_*` field lemmas exist, and no absolute-envelope seam lemma exists (only the
     visited-set `seamCompTM_visitedByTapeHead_ofCfg`). So the private seam, select, emit, halt,
     record and summary helpers are not library facts.
2. **In-context probe (copy A).** `mk_copyA.py` puts `exact?` in place of each of 47 candidates
   (`copyA_tags.tsv`). The run finished in 152 s (`copyA.log`).
   * The lean CLI prints a successful `exact?`'s `Try this` info without a position. I matched
     those infos to probes in message order.
   * Two probes hit the 400000 cap: A27 and A32a. Each timeout aborts its whole declaration, so
     three later probes in the same declarations gave no message (A28, A33, A34).
   * The timeout in `sph_valid_machine` also produces the kernel "unknown constant" at 2225. That
     is a cascade, not a finding.
   * I reran A28, A33 and A34 alone (`HA2.lean`, `copyA2.log`, 151 s).
3. **Generalised probe (file B).** `HB.lean` has 46 standalone `example`s under the file's nine
   imports (`copyB.log`, 86 s, `copyB_tags.tsv`).
4. **Name checks, term checks, `apply?` (file B2).** `HB2.lean` (`copyB2.log`, 72 s, exit 0; 0.35 MB
   because of the `apply?` listings) contains:
   * 31 `#check`s, all resolved;
   * 20 term checks of the proposed replacements, all accepted;
   * `apply?` on the six open statements. None of them gives a closing suggestion: the square
     below `2^L`, the `|a| ≤ |a - b| + |b|` triangle step, the preimage form, the `foldl`/`all`
     fold, the right-move endpoint, and the `logSpace` domination.
5. **Judgement.** I used the G5 rule.
   * A **hit** is a site whose inline proof re-establishes one published lemma, where the lemma
     states the fact or a direct specialisation, and its arguments are hypotheses or at most one
     further lemma.
   * The **M class** covers an `omega` witness, or two chained citations, that make exactly one
     published lemma.
   * An **idiom** is a site that already cites the lemma and only adapts its shape, or a decision
     procedure closing a residual goal.
   * **Not a library fact** means no lemma states it.
6. **Replacement test.** `mk_copyC.py` applies the replacements. Each old text must occur the
   stated number of times, and added lines over 100 characters are flagged (none). The modes are:
   * default → copy C;
   * `--no-M` → copy CG;
   * `--optional` → copy D;
   * `--heartbeats` → the probe-copy option, used for the elaborated copies.

## Candidate table

A = copy A (in context), B = file B (generalised), B2 = name/term checks. ✓ = closed by the lemma
named; ✗ = `exact?` could not close; "cap" = hit the 400000 heartbeat cap.

| line | declaration | step | candidate lemma | how found | verdict |
|---|---|---|---|---|---|
| 167–175 | `sph_inclusion` | the whole statement | – | B08 ✗ (also the pre-ship `HDupProbe`) | not a library fact |
| **168–169** | `sph_inclusion` | `hfloor : ∀ n, 1 ≤ g n` | `Nat.one_le_of_lt` | A01 ✗ (the `∀` binder); A41/B06 ✓ on the pointwise form | **M5** |
| 174 | `sph_inclusion` | `simpa using this` (`1 * f n ≤ g n`) | – | A02 ✗, B43 ✗ | idiom (`one_mul`) |
| 175 | `sph_inclusion` | `Nat.le_mul_of_pos_left _ (Nat.succ_pos _)` | – | – | citation |
| **177–179** | `sph_inclusion` | calc steps 2–3 | `Nat.le_mul_of_pos_right` | **A03 ✓**; B42 ✗ on the whole branch (the `omega` side) | **hit G1** |
| 207–250 | `sph_code_window` | normal form, coding, simulation, window | `exists_codeTM_spaceUsed`, `decode_encode`, … | reading | citations (the review's M4 route) |
| 219–221 | `sph_code_window` | `hx`, residual goal | `Nat.le_add_left` | A04 ✓ (residual); B46 ✗ (whole) | idiom; **O6** |
| **234–235** | `sph_code_window` | `hfloor` for `f` | `Nat.one_le_of_lt` | as 168 | **M5** |
| 236–241 | `sph_code_window` | `hsmall` | – | – | idiom (`calc` + `ring`) |
| 255–261 | `sph_sq_le_two_pow` | `4 ≤ L → L * L ≤ 2 ^ L` | – | A05 ✗, B01/B02 ✗, B2 `apply?` none | not a library fact |
| 267–278 | `sph_logSpace_dom` | `A * logSpace n ≤ n + 1` eventually | – | B03 ✗, B2 `apply?` none | not a library fact |
| 288–290 | `sph_logspace_ssubset` | `hlin : SPACE (n+1) ⊆ PSPACE` | – | A06 ✗, B04 ✗; B2 T13 `SPACE_succ_pow_subset_PSPACE 1` (same length) | citation (`space_poly_subset_PSPACE 1` + `pow_one`) |
| 303–333 | `sphRightTM`, `sph_right_run` | one-step leaf, field reading | – | grep: the published leaves are `Bool`-only | not a library fact |
| 335–340 | `sph_right_run` | `1 ≤ (moveInputPos p .pos).val` | `LogProg.moveInputPos_val` | A07 ✗, B11 ✗, `apply?` none; B2 T07 ✓ (+ `omega`) | alternative route; **O7** |
| **342** | `sph_right_run` | `u = 0` | `Nat.lt_one_iff` | **A08a ✓**, B09 ✓ | **M1** |
| 345 | `sph_right_run` | `decide` | – | – | idiom |
| **347** | `sph_right_run` | `u = 0 ∨ u = 1` | `Nat.le_one_iff_eq_zero_or_eq_one` | **A09a ✓**, B10 ✓ | **M2** |
| 354–381 | `sphEmitTM`, `sph_emit_run` | emitter leaf | – | grep (no non-`Bool` emitter) | not a library fact |
| **384** | `sph_emit_run` | `u = 0 ∨ u = 1` | as 347 | **A09b ✓** | **M2** |
| 389–429 | `sphDigit`, `sph_fold_valid` | the fold accepts exactly digit images | – | B40 ✗, B45 ✗, B2 `apply?` none | not a library fact |
| 412, 426 | `sph_fold_valid` | `Bool.and_eq_true_iff`, `List.cons.inj` | – | – | citations |
| 437–453 | `sph_validation_run` | wraps `inputFoldTM_run_ofCfg` | – | – | citation |
| 457–461 | `sphWitnessSel` | `⟨KI+KR+2+i, _⟩` | `Fin.natAddEmb` + a cast | reading | no hit (needs a cast; 471/1990 unfold the def) |
| **462–464** | `sphWitnessSel.inj'` | `omega` from `a + i = a + j` | `Nat.add_left_cancel` | **A10 ✓**, B12 ✓ | **M4** |
| 467–472 | `sph_witness_cap` | – | – | – | TCSlib |
| 516–531 | `sph_radius_run` | `hs`, `ho`, `hc`, `hh`, `hl` | – | – | citations |
| 535–540 | `sph_radius_run` | `hout'` map congruence | `rfl` | A11 `rfl`; B36 `rfl` | definitional; **O4** |
| 555, 594 | `sph_radius_run` | `lt_or_eq_of_le` | – | – | citation |
| **560–589** | `sph_radius_run` | per-tape sum ≤ card · r | `Finset.sum_le_card_nsmul`, `Finset.card_fin`, `smul_eq_mul` | A12 ✗ (constant step); B13/B14 ✗; **B38 ✓**; B2 T03/T04 ✓ | **hit G8** |
| 577, 583, 586, 604, 614, 617 | `sph_radius_run` | residual `omega`/`push_cast` | – | – | idiom |
| **616** | `sph_radius_run` | `hn : (0:ℤ) ≤ ↑n` | `Int.natCast_nonneg` | **A13 ✓**, B15 ✓ | **M3** |
| **621–623** | `sphEmptySel` | `Fin 0 ↪ Fin k` | `Function.Embedding.ofIsEmpty` | **B28 ✓** (A n/a: a `def`) | **hit G7** |
| 631–683 | `sph_input_rewind_run` | R1 reconstruction | – | – | citations (`embedEmitCfg_eq`, `inputRewindTM_run`, …) |
| 641, 646, 653, 654 / 670, 672, 673 | `sph_input_rewind_run` | `simpa [length_map]`, `Fin.ext rfl`, `List.append_nil`, `Fin.elim0` | – | – | idiom / citation |
| 700–717 | `sph_seam_heads` | absolute envelope through a seam | – | grep (visited-set versions only) | not a library fact |
| 715 | `sph_seam_heads` | `∃ w ≤ v, u = t+1+w` | – | A14 ✗, B19 ✗ | not a library fact (bounded witness) |
| 725–831 | `sph_rewinds_run` | seams and rewinds | – | – | citations |
| 783–801 | `sph_rewinds_run` | `hend` (`Cfg.ext` on `d₃.mapState`, nontrivial fields) | – | – | idiom (not the K1 shape) |
| 811, 817, 830 | `sph_rewinds_run` | `rw [_, sub_self, abs_zero]; omega` | – | – | idiom (residual `0 ≤ ↑n`) |
| 839–860 | `sph_select_fields` | `Cfg.select` field readings | – | grep (no `Cfg.select_*`) | not a library fact |
| **863–866** | `sphInitSel` | `⟨i.val, _⟩` embedding | `Fin.castLEEmb` | reading; Mathlib source; copy C ✓ | **hit G9** |
| 907–908, 1132 | `sph_initial_record`, `sph_test_run` | `h0`/`h1` | – | – | definitional |
| 921 | `sph_initial_record` | `(by have := j.isLt; exact this)` | `j.isLt` | A15 ✗ (the goal is `(ι j).val < _`) | cosmetic; **O5** |
| 938, 1064, 1157 | three runners | `simp only [sub_self, abs_zero, Nat.cast_nonneg]` | – | – | idiom |
| 948, 1080 | `sph_initial_record`, `sph_runner_run` | `hz` via `ι.injective.eq_iff` | – | – | citation |
| 963–972 | `sphRunnerSel` | piecewise embedding | – | – | not a library fact |
| **1027** | `sph_runner_run` | `hz : i.val ≠ 0` | `Fin.val_ne_zero_iff` | **A16 ✓**, B16 ✓ | **hit G2** |
| **1042** | `sph_runner_run` | `0 < i.val` (inner lambda) | `Fin.val_ne_zero_iff` | A17 ✗ (whole), B17 ✗; B2 T06 ✓ (also `Fin.pos_iff_ne_zero.mpr hi`) | **hit G2** |
| 1096–1098 | `sphRecordSel` | `Fin 1 ↪ Fin (k+1)`, `toFun _ := 0` | `Fin.castLEEmb` | reading; copy D ✓ | extensional only; **O8** |
| **1180** | `sphEmitContract.cut` | `u = 0` | `Nat.lt_one_iff` | **A08b ✓** | **M1** |
| 1187 | `sphEmitContract.env` | `Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩` | (`Finset.left_mem_Icc.mpr le_rfl`) | A18 ✗, B35 ✗; B2 T09 (same length) | idiom (published `framedContract` uses the same) |
| 1223–1243, 1264 | `sph_verdict_run` | contract fields, `ite_self` | – | – | citations |
| **1252–1260** | `sph_verdict_run` | `hp` `Cfg.ext` skeleton | `Cfg.mapState_mapState`, `Cfg.mapState_eq_of_fields` | A19 ✗; **B32/B44 ✓** | **hit K1** |
| 1268 | `sph_verdict_run` | `ht : t+2 = t+1+1` | `rfl` | A20 `rfl`; B37 `rfl` | definitional; **O1** |
| 1275–1296 | `sph_verdict_run` | `Cfg.ext` on a record update | – | – | idiom (not the K1 shape) |
| 1303, 2231 | two envelopes | `min_eq_left`/`max_eq_left` | – | – | idiom |
| 1313–1324 | `sph_summary` | stop-uniqueness reading | – | – | citations |
| 1322, 1711, 1467, 1499 | various | `WindowExit.noConfusion` | – | – | idiom |
| 1344, 1453, 1462, 1478 | various | `Option.map_injective Sum.inl_injective` | – | – | citation |
| **1349** | `sph_seam_avoids` | `∃ w, u = t + 1 + w` | `Nat.exists_eq_add_of_le` | A21 ✗, B18 ✗; **B2 T05 ✓** | **M6** |
| **1351–1353** | `sph_seam_avoids` | right-segment state is not left | `Option.map_eq_some_iff`, `Sum.inr_ne_inl` | A22 ✗, B34 ✗; **B2 T08 ✓** | **M8** |
| 1361–1390 | `sph_written_record` | layout boundary argument | – | – | not a library fact (`recordAt_iff` cited); 1385 `omega` split idiom |
| 1412–1551 | `sph_runner_tail_run` | three-exit seams | – | – | citations |
| 1583–1608, 1619–1663 | `sph_suffix` | runner, test, record readings | – | – | citations |
| **1610–1618** | `sph_suffix` | `hstart` `Cfg.ext` skeleton | as K1 | A23 ✗; B32 ✓ | **hit K1** |
| 1625–1626, 1821–1822 | `sph_suffix`, `sph_record_suffix` | `hRB`, `hTB`, `hIB` | – | – | citations |
| **1668–1676** | `sph_suffix` | `hmaps` `Cfg.ext` skeleton | `Cfg.mapState_mapState` + `rfl` | A24 ✗; in-file precedent 1959/1994 | **hit K1** |
| 1683–1686 | `sph_suffix` | `decide_eq_decide` | – | – | citation |
| **1756–1761** | `sph_record_suffix` | `hstart` `Cfg.ext` skeleton | as K1 | A25 ✗; B32 ✓ | **hit K1** |
| **1775–1777, 1790–1795** | `sph_record_suffix` | `(0 : Fin _) ≠ 1` ×3 | `Fin.zero_ne_one` | **A26a–c ✓**, B20 ✓ | **hit G3** |
| 1781, 1815 | `sph_record_suffix` | `j ≠ 1` from a bound | – | – | idiom |
| 1813 | `sph_record_suffix` | `hj0 : j ≠ 0` from `KI + 2 ≤ j.val` | – | A27 cap, B41 ✗ | not a library fact |
| **1823–1825** | `sph_record_suffix` | `hSB` two-step `trans` | `Nat.mul_le_mul` | A28 ✗ (`B` is a `let`, A2); **B29 ✓** | **M7** |
| **1853** | `sph_record_size` | `hfloor` | `Nat.one_le_of_lt` | B06 ✓ | **M5** |
| **1854** | `sph_record_size` | `hb : (g n).bits.length ≤ g n` | `length_bits_le_self` | **A29 ✓**, B22 ✓ | **hit G5** |
| 1855–1863 | `sph_record_size` | `posWidth n ≤ 2 * g n` | – | B30 ✗ | not a library fact |
| 1857–1859 | `sph_record_size` | `hpow : n+1 < 2^(log n + 2)` | – | A30 ✗, B31 ✗ | idiom (two citations, no single lemma) |
| **1865** | `sph_record_size` | `hk : k ≤ k * g n` | `Nat.le_mul_of_pos_right` | **A31 ✓**, B21 ✓ | **hit G4** |
| 1866, 2052, 2398 | three arithmetic closes | `nlinarith` | – | – | idiom |
| 1913–1947 | `sph_valid_machine` | `hstart` (`embedSilentCfg` readings) | – | – | idiom |
| 1957–1960, 1993–1995 | `sph_valid_machine` | `hwi`, `hai` | – | – | already cite `Cfg.mapState_mapState` |
| 2014–2020, 2025–2030 | `sph_valid_machine` | `\|a\| ≤ \|a - b\| + \|b\|` via `abs_sub_le` | – | A32a cap, A33 ✗ (A2), B23 ✗, B2 `apply?` none | idiom |
| **2048** | `sph_valid_machine` | `hbits` | `length_bits_le_self` | **A34 ✓** (A2) | **hit G5** |
| **2049** | `sph_valid_machine` | `hfloor` | `Nat.one_le_of_lt` | B06 ✓ | **M5** |
| 2067–2092 | `sph_halt_contract` | first-halt contract | – | grep | not a library fact |
| **2136** | `sph_validated_machine` | `hrad : (0:ℤ) ≤ ↑radius` | `Int.natCast_nonneg` | **A35 ✓** | **M3** |
| 2159–2164 | `sph_validated_machine` | `hstart₁` `Cfg.ext` skeleton | `rfl` | A36 `rfl`; B33 `rfl` (`Cfg.init`) | definitional; **O2** |
| 2184 | `sph_validated_machine` | `heq` from mapped words | – | A37 ✗, B39 ✗ | citation (`List.map_injective_iff`) |
| 2200–2201 | `sph_validated_machine` | `ScanPhase.done true ≠ .done false` | – | A38 `not_eq_of_beq_eq_false rfl` | idiom |
| 2216–2221 | `sph_validated_machine` | `hpre` `Cfg.ext` skeleton | `rfl` | A39 `rfl` | definitional; **O3** |
| 2304–2329 | `sph_diagonal_language` | leaf and acceptance readings | – | – | citations |
| **2332–2333** | `sph_diagonal_language` | `hind` 4-way case bash | `Bool.eq_iff_iff` / `Bool.coe_iff_coe` | **A40 ✓**, B24/B25 ✓ | **hit G6** |
| **2346** | `sph_diagonal_language` | `hn : 1 ≤ g n` | `Nat.one_le_of_lt` | **A41 ✓** | **M5** |
| 2347–2350 | `sph_diagonal_language` | `hb` `calc` | – | – | idiom (`ring`) |
| 2381–2391 | `sph_linear_ne_NP_of_padding` | `hpull : p ⁻¹' L' = L` | (`Set.preimage_image_eq`) | A43 ✗, B27 ✗, B2 `apply?` none | no hit (`L'` is `{y \| ∃ x ∈ L, y = p x}`, not `p '' L`) |
| 2387–2388 | `sph_linear_ne_NP_of_padding` | `he : x = y` | – | A42 ✗, B26 ✗; B2 T11 via `pairEncode_injective` (not shorter) | citation (`pairFstD_pairEncode`) |
| 2515–2517 | `space_hierarchy` | final `simp only` | – | – | idiom |

**Repetition within the file** (out of scope; not library re-derivations):

* the R1 `hrun` reconstruction (`embedEmitTM_runFrom` + `embedEmitCfg_select`, 4 copies);
* the selected-envelope block with `simp only [sub_self, abs_zero, Nat.cast_nonneg]` (3 copies);
* the `RecordAt` transport through `mapState` (`recordAt_iff` + `mapState_workTapes`/`_workTapePos`,
  5 copies);
* the logarithmic floor (5 copies, M5);
* the `(0 : Fin _) ≠ 1` proof (3 copies, G3).

## Elaboration outputs

| file | content | result |
|---|---|---|
| `base.log` | `HBase.lean`, unmodified copy (`cmp`-identical) | exit 0; `sorry` at 147:8 and 2560:8 only; 7 s |
| `base4.log` | `HBase4.lean`, unmodified except `maxHeartbeats 400000` | exit 0; the same two warnings; 6 s |
| `copyA.log` | `HA.lean`, 47 in-context probes | exit 1 (probe messages only, plus the cascade at 2225); 152 s |
| `copyA2.log` | `HA2.lean`, A28/A33/A34 alone | exit 1 (probe messages only); 151 s |
| `copyB.log` | `HB.lean`, 46 generalised probes | exit 1 (probe messages only); 86 s |
| `copyB2.log` | `HB2.lean`, names, term checks, `apply?` | exit 0 (`apply?` leaves `sorry` warnings); 72 s |
| `copyC.log` | **`HC.lean`: G1–G9, K1, M1–M8** | **exit 0; `sorry` at 147:8 (`space_universal`) and 2521:8 (`SPACE_linear_ne_NP`) only; 8 s** |
| `copyCG.log` | `HCG.lean`: G1–G9, K1 only | exit 0; the same two warnings (147:8, 2522:8); 8 s |
| `copyD.log` | `HD.lean`: copy C + O1–O8 | exit 0; the same two warnings (147:8, 2504:8); 7 s |

The elaborated copies `HC`/`HCG`/`HD` carry the probe option `maxHeartbeats 400000` at line 16.
The diffs and `HierarchyC/CG/D.lean` here keep the file's `maxHeartbeats 0`. Otherwise they are
identical to the elaborated copies (`diff` shows only line 16). Passing at 400000 implies passing
at the file's unbounded setting.

## Files

* `README.md` (this file); `copyC.diff` (the deliverable), `copyCG.diff`, `copyD.diff`.
* `HierarchyC.lean`, `HierarchyCG.lean`, `HierarchyD.lean`: the patched files, with line 16 as in
  the source.
* `mk_copyA.py` (an optional third argument selects probes), `mk_copyC.py` (`--no-M`,
  `--optional`, `--heartbeats`), `closure.py`.
* `Hierarchy.src.lean` (the target at `14ee2e46`), `all_sites.txt`, `closure.txt`,
  `copyA_tags.tsv`, `copyA2_tags.tsv`, `copyB_tags.tsv`.
* Logs: `base.log`, `base4.log`, `copyA.log`, `copyA2.log`, `copyB.log`, `copyB2.log`, `copyC.log`,
  `copyCG.log`, `copyD.log`.
* Scratch Lean (git-excluded), in `wt-hk/rvprobe/hsweep/`: `HBase.lean`, `HBase4.lean`, `HA.lean`,
  `HA2.lean`, `HB.lean`, `HB2.lean`, `HC.lean`, `HCG.lean`, `HD.lean`.
