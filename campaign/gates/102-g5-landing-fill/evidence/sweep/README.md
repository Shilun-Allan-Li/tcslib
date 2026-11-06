# Library re-derivation sweep of `TwoTapes.lean`

Target: `TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean` at branch
`deliver/fill-u2s-g5-in` (`71046be0`) of `/home/user/tcslib`. The file has 2,464 lines. All line
numbers below are lines of that source, which is copied here as `TwoTapes.src.lean` (`cmp`-identical
to `git show`).

Nothing tracked was edited, committed or pushed: `git status --short` is empty in both
`/home/user/tcslib` and `wt-hk`. Scratch Lean files are in `wt-hk/rvprobe/g5sweep/`, which is
git-excluded through `rvprobe/`.

Lean was run only as
`bash /home/user/tcslib/devtools/seyoon/leanelab.sh /home/user/tcslib-scratch/wt-hk /home/user/tcslib-scratch/oleans-lnth rvprobe/g5sweep/<File>.lean`,
one elaboration at a time. Each command was prefixed by `. /home/user/tcslib-scratch/env.sh`, and
the scripts were run with `python3 -I`. Each log ends with `-- exit=N, T s (snapshot oleans-lnth)`.

## Result

**Eight clear hits (G1–G8), one rewrite-chain hit (K1), five borderline hits (M1–M5), and one hit
that needs an import (I1).** All of them are applied together in copy C (`TtC.lean`,
`copyC.diff`: 21 hunks, +42 −65). Copy C **elaborates with exit 0 and no messages**, the same as
the unmodified baseline.

Two variants also elaborate with exit 0 and no messages:

* copy C0: copy C without I1, so with no new import;
* copy D: copy C plus three optional cosmetic items.

| id | line(s) | inline proof | published lemma (replacement) |
|---|---|---|---|
| **G1** | 1421–1424 (private `tt_output_map`; uses 1478, 1523; docstring 1436) | `cases a.output <;> rfl` | `Option.toList_map` (core; the same `cases` proof). The private theorem is dropped and both `rw` lists cite the core lemma. |
| **G2** | 2023–2028 `hinj` | strict monotonicity ⇒ injective, by `by_contra` + `lt_or_gt_of_ne` | `StrictMonoOn.injOn hstep` |
| **G3** | 2029–2032 card `calc` steps 1–2 | `card_image_of_injOn` + `card_le_card` of the image | `Finset.card_le_card_of_injOn (fun a => a / g) (maps-to) hinj` |
| **G4** | 1604–1607 `hsum` | `sum_const` rewrite chain + `Finset.sum_le_sum` | `Finset.card_nsmul_le_sum`, then `rwa [Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm (t' + 1) 2]` |
| **G5** | 1142, 1155, 2180, 2202 (4 sites) | `fun h => ht (Fin.ext h)` | `Fin.val_ne_of_ne ht` (core, whose body is the same term) |
| **G6** | 813 `tt_full_empty` | `fun i => absurd i.isLt (Nat.not_lt_zero _)` | `fun i => i.elim0`. Core `Fin.elim0` is defined as `absurd h (not_lt_zero _)`: verbatim. |
| **G7** | 101–105 `hb` | `calc t ≤ t+1 = (t+1)*1 ≤ (t+1)*(L+1) = 1*(…)` | `rw [Nat.one_mul]; exact le_mul_of_le_of_one_le (Nat.le_succ t) (by omega)`. Mathlib's proof of `le_mul_of_le_of_one_le` is this same three-step calc. |
| **G8** | 555–558 `obtain ⟨s', hs'⟩` | `cases h : … with \| none => … \| some s' => …` | `Option.ne_none_iff_exists'.mp (ne_of_mem_of_not_mem hx (F.none_nmem _ _))`. The file cites `Option.ne_none_iff_exists'` six times elsewhere. |
| **K1** | 2384–2385 `simp only` list | `Finset.card_univ, Fintype.card_fin` and `nsmul_eq_mul, Nat.cast_id` | `Finset.card_fin` and `Nat.nsmul_eq_mul`: each pair composes to the one lemma |
| M1 | 1859 `hidx` | `le_antisymm h (not_lt.mp hlt)` | `eq_of_le_of_not_lt h hlt` |
| M2 | 2220 `hidx` | the same | `eq_of_le_of_not_lt (zoneRebalanceIndex_le _ _ _) hlt` |
| M3 | 2343 `obtain ⟨s, rfl⟩` | `⟨t₀ - 1, by omega⟩` | `Nat.exists_eq_add_one.mpr h1` (core) |
| M4 | 2118 `hpow` | `rw [hn, pow_succ]; ring` | `rw [hn, pow_succ']` |
| M5 | 1879–1897 private `tt_Dtr_level_mono` | `Nat.le_induction` with `ih.trans` (the generic skeleton) around the one-step fact | `monotone_nat_of_le_succ` applied to the one-step fact, as `ZoneRebalance.lean:8213` already does |
| I1 | 2318–2323 private `tt_sum_range_fin` (use 2386) | `Finset.sum_bij` | `Finset.sum_range` / `(Fin.sum_univ_eq_sum_range f k).symm`. **Neither lemma is in the import closure.** Copy C adds `import Mathlib.Data.Fintype.BigOperators`, drops the private theorem and rewrites with `← Fin.sum_univ_eq_sum_range (…) M.k`. |

The M items are the borderline class, like the dpsweep's M1–M3 and the earlier G4: two chained
citations, or an `omega` witness, that are exactly one published lemma. The maintainer can take G
and K alone, which means dropping the M hunks from `copyC.diff`. Every hunk keeps its `have` or
`theorem` statement unchanged, so the hunks are independent. I1 is the only change that adds an
import: take it, or leave it and record the private theorem as a known duplicate. Copy C0 shows
that the rest elaborates without it.

## Method

1. **Enumeration.** I read the whole file. `all_sites.txt` (from `grep -nE`, 686 lines) lists every
   `have`, `obtain`, `private theorem`, `calc` step, anonymous `have :=`, and `rw`/`simp only` list.
   * The 27 anonymous `have :=` sites (859 … 2399) are all citations of one lemma or hypothesis.
     The one exception is 1786, an `omega` bridge from `Finset.mem_range`.
   * The `obtain … : stmt` sites are 71, 73, 555, 583, 729, 786, 2343.
   * I kept the statements about core/Mathlib objects (generalised where needed) and the TCSlib
     facts that a published lemma might state.
   * For the TCSlib facts I computed the import closure (`closure.py` → `closure.txt`, 24 TCSlib
     modules) and ran `git grep` at the branch. I searched for:
     * `runFrom … 1` (only private copies elsewhere: `xr_runFrom_one`, `recordStep_runFrom_one`);
     * the `workTapeSymbols` function form (`Cfg.workTapeSymbols_eq` is pointwise; `hW` is `rfl`);
     * `initCfg_*` field lemmas (none);
     * mapped-input `inputSymbol` lemmas (`Cfg.inputSymbol_congr` needs the same input);
     * `moveInputPos` across lengths (none);
     * gap/card lemmas (none);
     * the published `zoneShiftIndex_*`, `zoneCascade*_lengths`, `zoneRebalance_frame` and
       `ZoneContents.*` lemmas of `Zone.lean`. These are cited, not re-derived.
2. **In-context probe (copy A).** `mk_copyA.py` puts `exact?` in place of each of 22 candidates.
   * The file sets `maxHeartbeats 0`. A tactic-level `set_option … in` does not bound `exact?`
     under it (dpsweep). So copy A replaces the file-level option by `set_option maxHeartbeats
     400000`, and every probe also carries `set_option maxHeartbeats 400000 in`.
   * Before that, I checked that the unmodified file elaborates under 400000 (`base4.log`: exit 0,
     no messages, 10 s). So no proof in it needs the unbounded setting.
   * Copy A finished in 86 s (`copyA.log`, line map `copyA_tags.tsv`).
3. **Generalised probe (file B).** `TtB.lean` has 50 standalone `example`s under the file's four
   imports, each with `set_option maxHeartbeats 400000 in` (`copyB.log`, 55 s; `copyB_tags.tsv`).
4. **Normalised cores (file B2).** `TtB2.lean` (`copyB2.log`, 35 s; 0.6 MB because of `apply?`
   listings):
   * `#check`s the expected names;
   * term-checks each proposed replacement;
   * runs `exact?` on the cores `b ≤ c → 1 ≤ a → b ≤ c * a` and `0 < n → m ≤ m * n`;
   * runs `apply?` on the open statements.

   `exact?` misses `eq_of_le_of_not_lt`, `Fin.elim0` and `monotone_nat_of_le_succ` (the conclusion
   is too general, or `Monotone` is unfolded). B2 checks each of them by term instead.

   `TtB3.lean` (`copyB3.log`) then established which names the closure has:
   * **missing:** `Finset.sum_range`, `Fin.sum_univ_eq_sum_range`, `Fin.sum_const`,
     `smul_eq_mul`;
   * **present:** `Nat.nsmul_eq_mul`, `Finset.card_fin` and every lemma that copy C uses without
     an import.
5. **Judgement.** I used the previous sweeps' rule. A site is a **hit** when the inline proof
   re-establishes one published lemma whose statement is the fact or a direct specialisation, and
   the lemma's arguments are hypotheses or at most one further library lemma. It is an **idiom**
   when the proof already cites the relevant lemma and only adapts its shape, or when it is a
   decision procedure (`omega`, `ring`, `nlinarith`). It is **not a library fact** when no lemma
   states it.
6. **Replacement test.** `mk_copyC.py` applies the replacements; each old text must occur the
   stated number of times:
   * default → copy C;
   * `--no-import` → copy C0;
   * `--optional` → copy D.

   No added line is over 100 characters; the 37 long lines are pre-existing.

## Candidate table

A = copy A (in context), B = file B (generalised), B2/B3 = name/term checks. ✓ = closed by the
lemma named; ✗ = `exact?` could not close.

| line | site | statement (generalised) | A | B / B2 | disposition |
|---|---|---|---|---|---|
| 71 | `obtain ⟨σ⟩` | `Nonempty (Fin k ↪ Fin 2)` | – | – | citation (`Fin.castLEEmb`) |
| 73–93 | `obtain ⟨N,…⟩`, `hinit` | host restart, initial embedding | – | – | TCSlib content (`initCfg_with_q₀`, `embedEmitCfg_eq`) |
| 89–90 | bullet | `i : Fin M.k`, `M.k = 0` ⊢ … | `Prod.mk_inj.mp rfl` (defeq) | B07 ✗ | idiom; optional O1 `(i.cast hk).elim0` |
| **101–105** | `hb` | `t ≤ 1 * ((t+1)(L+1))` | ✗ | B01 ✗; **B2 D01 `le_mul_of_le_of_one_le h ha`**; D02 `Nat.le_mul_of_pos_right` | **hit G7** |
| 149–150 | `hinl` | `⇑Embedding.inl = Sum.inl` | `rfl` | B02 `rfl` | definitional; no published lemma (`@[simps]` gives `inl_apply` only) |
| 289–290 | `hW` | `c.workTapeSymbols = fun i => …` | – | B03 `rfl` | TCSlib transport of `Cfg.workTapeSymbols_eq` (definitional) |
| 302, 306, 1141, 2161 | `rw` chains | `Option.getD_none, update_eq_self`; `SignType.coe_zero, add_zero` | – | B29 ✗, B34 ✗ | idiom (no single lemma) |
| **555–558** | `obtain s'` | `o ∈ X → none ∉ X → ∃ s, o = some s` | ✗ | B04 ✗; B04b `Option.ne_none_iff_exists'.mp`; B04c `ne_of_mem_of_not_mem`; D08 term ✓ | **hit G8** |
| 559, 1563 | `hs'X`, `h0` | `▸` transports | – | – | idiom |
| 707–710 | `hr`, `hR` | `update_self`; `funext hread` | – | – | citations |
| 722–724 | `h1` | `runFrom c 1 = step c` | `rfl` | B05 `rfl` | definitional; no published `runFrom_one` |
| 729, 1368 | `obtain rfl` | `Option.some.inj` | – | – | citation |
| **813** | `tt_full_empty` | `∀ i : Fin 0, P i` | ✗ | B06 ✗; D04 `fun i => i.elim0` ✓ | **hit G6** (core `Fin.elim0` body verbatim) |
| 832–833, 884, 949 | `by ring` | capacity arithmetic | – | – | idiom (`ring`) |
| 858–866, 923–931, 984–990, 1012–1018, 1671–1677, 1729–1735 | `hr`/`hl`/`hne` | `zoneShiftIndex_empty/_nonempty` through `words_*` | – | – | TCSlib citations. Repeated in-file but out of scope; `Zone.lean` publishes no specialised form. |
| 863, 928, 987, 1015, 1644 | `rwa […, List.length_nil, add_zero]` | `a + [].length = a` | – | B30 `rfl` | idiom (no single lemma) |
| 867, 932, 990, 1018, 1677, 1735 | `hpos` | `List.length_pos_iff.mpr` | – | – | citation |
| 869–875, 934–940, 991–998, 1019–1026, 1696–1701, 1754–1760 | `hc`/`hsum'`/`hcase'`/`hdonor`/`hroom` | fullness arithmetic | – | – | TCSlib + `omega` |
| **1038** | `hpow` | `2^(j-1) ≤ 2^j` | ✗ | B08 ✗; D09 `apply?`: no closing lemma | idiom (cites `Nat.pow_le_pow_right`; `omega` side goal) |
| 1101, 1864 | `Nat.lt_succ_self` | – | – | – | citation |
| 1111–1115 | `tt_shift_dir` | TCSlib | – | – | not a library fact |
| **1142, 1155, 2180, 2202** | `this : t.val ≠ j` | `t ≠ ⟨j,_⟩ → t.val ≠ j` | ✗ (×4) | B09 ✗; **B09b `Fin.val_ne_of_ne ht`**; D18 term ✓ | **hit G5** (×4) |
| 1189, 1268, 1366, 1564, 2266 | `rw` chains | `runFrom_zero, initCfg_eq, Cfg.init_*` | – | grep: no composite | TCSlib, no composite lemma |
| 1271, 1445, 1511, 2270 | `hc`/`hstep` | `runFrom_succ_eq_step'` | – | – | citation |
| 1289–1292 | `tt_moveInputPos_val` | `moveInputPos` across equal lengths | – | grep: none | not a library fact |
| 1296–1315 | `tt_inputSymbol` | decoded input symbol on `x.map Sum.inl` | – | grep: `Cfg.inputSymbol_congr` is same-input only | not a library fact |
| 1299, 1320 | `hlen` | `List.length_map` | – | – | citation |
| 1309–1311 | `hp` | `omega` | – | – | idiom |
| 1393 | `this` | `p ≠ 0 → 1 ≤ \|p\|` | – | B36 `Int.one_le_abs` | citation (the inline is that lemma) |
| **1421–1424** | `tt_output_map` | `(o.map f).toList = o.toList.map f` | **`Option.toList_map`** | **B10 same** | **hit G1** |
| 1442, 1494 | `hlive` | `runFrom_state_ne_none_of_le` | – | – | citation |
| 1443, 1510, 1529, 2056, 2351 | `obtain ⟨q,hq⟩` | `Option.ne_none_iff_exists'.mp` | – | – | citation |
| 1559, 1567 | `hc`, `hl` | `rfl`, eta | – | – | trivial |
| 1569, 2344 | `Nat.add_sub_cancel` | – | – | – | citation |
| **1604–1607** | `hsum` | `(∀ r, 2 ≤ f r) → 2n ≤ ∑_{r<n} f r` | (1606) `Finset.sum_range_induction …` (not useful) | B11 ✗; **B11b `Finset.card_nsmul_le_sum s f 2 h`** | **hit G4** |
| 1606 | `rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]` | `2n = ∑_{r<n} 2` | as above | B12 ✗; B12b ✗; B3: `Nat.nsmul_eq_mul` | covered by G4 (`nsmul_eq_mul, Nat.cast_id` = `Nat.nsmul_eq_mul`) |
| 1622 | `tt_rsum_succ` | `sum_range_succ` + `dif_pos` | – | – | citations |
| 1646, 2117, 2127, 2225 | `h1`/`h2`/`h4` | `2 ≤ 2^(n+1)` | – | B35 ✗ | citation (`Nat.le_self_pow`) |
| 1647–1649, 1689, 1747, 1769, 2398 | `rw [pow_succ]; omega` | – | – | – | idiom |
| 1681, 1739 | `fun h' => absurd h' (Nat.not_lt_zero _)` | `j < 0 → P` | – | B32 ✗; D15 term | idiom (direct citation) |
| 1688, 1709, 1746, 1768, 2101, 2109 | `Nat.one_le_two_pow` | – | – | – | citation |
| 1695, 1753 | `hfin` | `Fin.ext hnj` | – | – | citation |
| 1707, 1766 | `hz0'` | `rw [hz0]; rfl` | – | – | TCSlib |
| 1786 | `hl'` | `l ∈ range n → n ≤ ℓ → l < ℓ` | – | B28 ✗ | idiom (`omega` bridge) |
| 1788–1796 | `hold`, extension | `extend_words_*` | – | – | TCSlib citations |
| 1838–1846, 1871–1872 | `push_cast; ring` | – | – | – | idiom |
| **1859** | `hidx` | `a ≤ b → ¬ a < b → a = b` | ✗ | B13 ✗ (exact? misses it); **D03 term `eq_of_le_of_not_lt` ✓** | **hit M1** (borderline) |
| **1879–1897** | `tt_Dtr_level_mono` | `(∀ j, f j ≤ f (j+1)) → j₁ ≤ j₂ → f j₁ ≤ f j₂` skeleton | – | B25 ✗; **D07 term `monotone_nat_of_le_succ hf h` ✓** | **hit M5** (borderline; structural) |
| 1901–1920 | `tt_Dtr_other` | `le_induction` under a disjunctive side condition | – | – | not a plain monotonicity; no library lemma |
| 1918 | `ht` | `(t < j₁ ∨ j+1 ≤ t) → j₁ ≤ j → t ≠ ⟨j,_⟩` | ✗ | B15 ✗, D17 ✗ | not a library fact |
| 1956–1971 | `hH1` … `hidx` | `rfl`, TCSlib citations | – | – | – |
| 2002 | `this` | `tt_shift dir = 1 ∨ = -1` | – | – | TCSlib |
| 2014 | `tt_card_le_of_gap` (whole) | gap-sparse set bound | – | B19 ✗, D14 `apply?`: none | not a library fact (contains G2, G3) |
| 2017–2022 | `hstep` | `0 < g → a + g ≤ b → a/g < b/g` | ✗ | B16 ✗; D10 `apply?` partial only; D10b ✗ | idiom (cites `Nat.add_div_right` + `Nat.div_le_div_right`) |
| **2023–2028** | `hinj` | `StrictMonoOn f S → InjOn f S` | **`StrictMonoOn.injOn hstep`** | **B17 same** | **hit G2** |
| **2029–2033** | card `calc` | maps-to + injOn ⇒ `card ≤ card` | **`Finset.card_le_card_of_injOn (fun a => a / g) hm hinj`** | **B18 same** | **hit G3** |
| 2084–2114 | `hlev`, `hdrift` | bounded `le_induction` | – | – | TCSlib; no library lemma |
| **2118** | `hpow` | `2^(i+1) = 2 * 2^i` | **`Nat.pow_succ'`** | B24 `Nat.pow_succ'` | **hit M4** (borderline: `pow_succ` + `ring` = `pow_succ'`) |
| 2122, 2129 | `exact_mod_cast hpow` | – | – | – | idiom |
| 2123, 2131 | `(1 : ℤ) ≤ 2^i` | `exact_mod_cast Nat.one_le_two_pow` | – | B31 ✗, D12 `apply?`: none closing | idiom (cast of a citation) |
| 2130, 2231 | `by ring` | `(2:ℤ)^(n+1) = 2 * 2^n` | – | B24b `Int.pow_succ'` | idiom (`ring`); optional O2/O3 `pow_succ'` |
| 2189–2194 | `hℓ` | `split_ifs; ring` | – | – | idiom |
| 2206–2210 | `hif` | if-congruence under `t ≠ j` | – | B33 ✗ | not a library fact |
| **2220** | `hidx` | as 1859 | ✗ | D03 | **hit M2** (borderline) |
| 2224, 2288 | `abs_le.mp/.mpr` | – | – | D11 `abs_le.mpr h` | citation; `hpos` (2283–2288) adds `linarith` for `0 ± r` (B23 ✗): idiom |
| 2240, 2292 | `le_max_of_le_right`, `max_le` | – | – | – | citation |
| 2311 | `h4` | `Nat.pow_le_pow_right` | – | – | citation |
| **2318–2323** | `tt_sum_range_fin` | `∑_{range k} f = ∑_{Fin k} f ∘ val` | ✗ (the lemma is not in the closure) | B20 ✗; B2/B3: `Finset.sum_range`, `Fin.sum_univ_eq_sum_range` **unknown in the closure** | **hit I1** (needs `import Mathlib.Data.Fintype.BigOperators`) |
| **2343** | `obtain ⟨s, rfl⟩` | `1 ≤ t → ∃ s, t = s + 1` | **`Nat.exists_eq_add_one.mpr h1`** | B21 same; B38 `Nat.exists_eq_succ_of_ne_zero` | **hit M3** (borderline: `omega` witness) |
| 2382–2383 | `hsumτ` | `sum_le_sum`, `sum_add_distrib`, `← mul_sum` | – | – | citations |
| **2384–2385** | `simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, mul_one]` | `∑ _ : Fin k, 1 = k` | – | B22 ✗; B22c `Finset.card_fin k`; B3 chain term ✓ | **hit K1** (two chains, each one lemma) |
| 2397–2400 | `hpow` | `2^(log t + 1) ≤ 2t` | – | B26 ✗; D13 `Nat.pow_log_le_self` | idiom (already cites it) |
| 2401 | `hlog` | `Nat.log_mono_right` | – | – | citation |
| 2403–2414 | `hP`, `hL3`, `e1`, `e2`, final | `nlinarith`/`omega`; e2 calc = `Nat.mul_le_mul_left` + `ring` | – | B27 ✗; B37 `Nat.mul_assoc` | idiom |
| 2448, 2461 | final assembly | citations | – | – | – |

## Optional (copy D = copy C + these; not hits)

| id | line | change | why optional |
|---|---|---|---|
| O1 | 90 | `exact absurd i.isLt (by omega)` → `exact (i.cast hk).elim0` | `Fin.elim0` after a `Fin.cast` transport; the inline is a one-liner with `omega` |
| O2 | 2130 | `by ring` → `pow_succ' 2 n` | `ring` one-liner (excluded class), but the statement is exactly `pow_succ'` |
| O3 | 2231 | `by ring` → `pow_succ' 2 E.1` | same |

## Elaboration outputs

| file | content | result |
|---|---|---|
| `base.log` | `TtBase.lean`, unmodified copy (`cmp`-identical) | exit 0, no messages, 11 s |
| `base4.log` | `TtBase4.lean`, unmodified except `maxHeartbeats 400000` | exit 0, no messages, 10 s |
| `copyA.log` | `TtA.lean`, 22 in-context probes | exit 1 (probe messages only), 86 s |
| `copyB.log` | `TtB.lean`, 50 generalised probes | exit 1 (probe messages only), 55 s |
| `copyB2.log` | `TtB2.lean`, cores, name checks, `apply?` | exit 1 (probe messages only), 35 s |
| `copyB3.log` | `TtB3.lean`, closure name checks | exit 1 (the missing names), 2 s |
| `copyC.log` | **`TtC.lean`: G1–G8, K1, M1–M5, I1** | **exit 0, no messages, 21 s** |
| `copyC0.log` | `TtC0.lean`: copy C without I1 (no new import) | exit 0, no messages, 23 s |
| `copyD.log` | `TtD.lean`: copy C + O1–O3 | exit 0, no messages, 23 s |

The C/C0/D runs took about twice as long as the baseline. They ran back to back while another
elaboration slot was in use, so the timing is not comparable. Each has no messages.

`copyC.diff` (21 hunks, +42 −65), `copyC0.diff` (19 hunks) and `copyD.diff` (24 hunks) are
unified diffs against the target path.

## Notes

* **The import closure is lean on BigOperators.** `Finset.sum_range`, `Fin.sum_univ_eq_sum_range`,
  `Fin.sum_const` and even `smul_eq_mul` are unknown under the file's imports. So the `smul` step of
  G4/K1 uses `Nat.nsmul_eq_mul`, and I1 needs `Mathlib.Data.Fintype.BigOperators`. The olean
  exists in the snapshot's Mathlib build, and copy C elaborates with it.
* **`exact?` blind spots on this file.** It finds neither `eq_of_le_of_not_lt` (an `Eq` conclusion
  with free sides), nor `Fin.elim0` (a dependent motive), nor `monotone_nat_of_le_succ`
  (`Monotone` unfolded). It also misses `Fin.val_ne_of_ne` in context (the goal has `j`, not
  `(⟨j, _⟩ : Fin k).val`). These were confirmed by term checks in B2. A future auditor running
  plain `exact?` would not find M1/M2/M5/G5/G6 either way. They were found by reading.
* **Definitional `rfl` sites** (149 `hinl`, 289 `hW`, 722 `h1`) are not re-derivations: no
  published lemma states them. They could be shortened to `rfl`, which is cosmetic.
* **In-file repetition**, out of scope: the `zoneShiftIndex_empty`/`_nonempty` + `words_*`
  transports (6 copies each), the `hdonor` fullness arithmetic (4 copies) and the `hif` blocks.
  These are reuse candidates within the file, not library re-derivations.

## Files

* `README.md` (this file); `copyC.diff`, `copyC0.diff`, `copyD.diff`.
* `mk_copyA.py` (an optional third argument selects probes) and `mk_copyC.py` (`--no-import`,
  `--optional`); `closure.py`.
* `TwoTapes.src.lean` (the target at `71046be0`), `all_sites.txt`, `closure.txt`,
  `copyA_tags.tsv`, `copyB_tags.tsv`.
* Logs: `base.log`, `base4.log`, `copyA.log`, `copyB.log`, `copyB2.log`, `copyB3.log`, `copyC.log`,
  `copyC0.log`, `copyD.log`.
* Scratch Lean (git-excluded), in `wt-hk/rvprobe/g5sweep/`: `TtBase.lean`, `TtBase4.lean`,
  `TtA.lean`, `TtB.lean`, `TtB2.lean`, `TtB3.lean`, `TtC.lean`, `TtC0.lean`, `TtD.lean`.
