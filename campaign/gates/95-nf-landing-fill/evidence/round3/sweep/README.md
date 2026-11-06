# Library-re-derivation sweep of `NDNormalForm.lean`

Target: `TCSlib/Complexity/ClassNP/NDNormalForm.lean` in worktree `wt-191`, branch
`lean/c1-nf-landing`, head `dfc3e99046ae130ea1b3abbb8fb6cc08fcfe7906` (3271 lines). All line numbers
below are lines of that source file. No tracked file was edited and nothing was committed
(`git status` in `wt-191` is clean). Scratch Lean files are in `wt-191/rvprobe/sweep/` (git-excluded).
Lean was run only through `leanelab.sh` against `oleans-lzsa2`, one elaboration at a time.

## Result in one paragraph

Eight inline proofs re-prove a published core/Mathlib lemma (G1–G8 below). Two recurring rewrite
chains are each a single library lemma: `rw [List.length_take, Nat.min_eq_left h]` is
`List.length_take_of_le h` (class K, 8 sites), and `rw [List.foldl_append, List.foldl_cons,
List.foldl_nil]` on `l ++ [x]` is Mathlib's `List.foldl_concat` (class F, 3 contiguous sites, plus 4
optional sites where the chain is split by other steps). Every replacement was applied together in
one scratch copy (`NFLibC.lean`), which elaborates with exit 0 and **no messages at all**, the same
as an unmodified baseline copy. The file is 35 lines shorter. The full diff is `copyC.diff`.

## Method

1. **Enumeration.** `all_haves.txt` lists every `have`, every `obtain … : stmt` and every
   `private theorem` (366 lines; produced with `grep -nE`). I kept as candidates the statements
   about core/Mathlib objects only. A statement qualifies when it mentions no `nf_*`,
   `Turing.*`/`Complexity.*` or other TCSlib definition, or reduces to one after generalising its
   free variables. I also kept the multi-step `rw [List.…]` chains that establish a list identity,
   and three core-only `split_ifs`/`refine` bullets (not `have`s, but the same kind of inline
   proof). I excluded pure `omega`/`ring`/term one-liners (listed under "Excluded").
2. **In-context probe (copy A).** `mk_copyA.py` copies the file and replaces each candidate proof
   *in place* by `exact? -- LIBSWEEP:<id>`, with everything else verbatim. That gives 32 probes in
   one copy. A failed `exact?` only sorries its own `have`, so the probes are independent.
3. **Generalised probe (file B).** `NFLibB.lean`: each candidate restated as a standalone `example`
   with its free variables as hypotheses, under the module's own seven imports, so the library
   searched is the same. 42 probes.
4. **Normalised-core probe (file B2).** `exact?` neither rewrites hypotheses nor takes a
   contrapositive. So for each B failure, `NFLibB2.lean` states the "core" the inline argument
   actually proves, after the one obvious hypothesis rewrite (e.g. `0 < a * b → 0 < b`). B2 also
   runs `apply?` on the remaining open arithmetic statement (C02).
5. **Judgement.** A candidate is **genuine** when the inline proof re-establishes the content of
   one published lemma whose statement is the `have` or a direct specialisation of it. The
   lemma's arguments may be hypotheses, a trivial transport of them (`trans_eq`, `▸`, `omega`), or
   at most one further library lemma applied to them. It is an **idiom** when the inline proof
   already cites the relevant library lemma and only adapts shape, when a library lemma does only
   part of the job, or when no library lemma covers the statement.
6. **Replacement test (copy C).** `mk_copyC.py` applies all proposed replacements at once. Each
   replacement keeps its `have` statement unchanged, so the replacements are independent of one
   another (F5a/F5b must go together). The first run failed in two places, where `▸` picked the
   wrong rewrite direction. I switched those, and for robustness the other direction-sensitive
   transports, to `LT.lt.trans_eq`, and re-ran.

Commands (each prefixed by `. /home/user/tcslib-scratch/env.sh;`):

```
cd /home/user/tcslib-scratch/agents/libsweep
python3 -I mk_copyA.py /home/user/tcslib-scratch/wt-191/TCSlib/Complexity/ClassNP/NDNormalForm.lean \
  /home/user/tcslib-scratch/wt-191/rvprobe/sweep/NFLibA.lean            # -> copyA_tags.tsv
bash /home/user/tcslib-scratch/wt-hk/devtools/seyoon/leanelab.sh /home/user/tcslib-scratch/wt-191 \
  /home/user/tcslib-scratch/oleans-lzsa2 rvprobe/sweep/NFLibA.lean  > copyA.log   # 3m43s
#   same for rvprobe/sweep/NFLibB.lean    > copyB.log    (52 s)
#   same for rvprobe/sweep/NFLibB2.lean   > copyB2.log   (18 s)
python3 -I mk_copyC.py <src> /home/user/tcslib-scratch/wt-191/rvprobe/sweep/NFLibC.lean
#   same for rvprobe/sweep/NFLibC.lean    > copyC.log    (21 s, exit 0, no output)
#   same for rvprobe/sweep/NFLibBase.lean > base.log     (unmodified copy: 19 s, exit 0, no output)
diff -u NDNormalForm.lean NFLibC.lean > copyC.diff
```

`exact?` reports a success as a position-less `Try this:` block, interleaved in order with the
failures' positioned errors. `copy*_tags.tsv` map lines to probe ids.

## Candidates and results

A = in-context `exact?` (copy A), B = generalised `example` (file B), B2 = normalised core
(file B2). ✗ = `exact?` could not close the goal.

| id | line | owner | statement (generalised) | A | B / B2 | disposition |
|---|---|---|---|---|---|---|
| C01 | 229 | `nf_display_flag` `hd` | `(W*(r+1)-1)/W = r` | ✗ | B01 ✗; D15 `Nat.div_eq_of_lt_le h1 h2` (bracket shape) | idiom: already cites `Nat.mul_sub_div` |
| C02 | 232 | `nf_display_flag` `hm` | `(W*(r+1)-1)%W = W-1` | ✗ | B02 ✗, D14 ✗; D16 `apply?`: `(Nat.mod_eq_sub_iff _ hW).mpr` leaves `W ∣ W*(r+1)-1+1` | idiom: lemma does only part |
| C03 | 261 | `nf_display_firstStop` `hipos` | `l.take i ≠ [] → i < l.length → 0 < i` | ✗ | B03 ✗; D05 only a congruence trick | idiom; contains K-chain (K1) |
| **C04** | 268 | `nf_display_firstStop` `hn` | `W*(i/W) = i → 0 < i → 0 < i/W` | ✗ | B04 ✗; **D01 `Nat.pos_of_mul_pos_left h`** | **genuine G2** |
| **C05** | 274 | `nf_display_firstStop` `hlt` | `i < W*n → i/W < n` | ✗ | **B05 `Nat.div_lt_of_lt_mul hi`** | **genuine G3** |
| C06 | 284–286 | `nf_display_firstStop` rw at `hb` | `(l.take i).getLastD d = l[i-1]?.getD d` | – | B06 ✗, D07 ✗ | idiom; contains K-chain (K2) |
| C07 | 300–301 | `nf_display_firstStop` rw | `l.getLastD d = l[l.length-1]?.getD d` | – | B07 ✗ | idiom (two library rewrites, no single lemma) |
| **C08** | 318 | `nf_firstStop_records` `hlen` | `L%W = 0 → L = W*(L/W)` | ✗ | B08 ✗; **D09 `Nat.mul_div_cancel' h`** (from `W ∣ L`) | **genuine G4** (composite, see below) |
| **C09** | 322 | `nf_firstStop_records` `hn` | `L = W*n → 0 < L → 0 < n` | ✗ | B09 ✗; **D01** | **genuine G5** |
| C10 | 332 | `nf_firstStop_records` `hmle` | `L = W*n → r < n → W*(r+1) ≤ L` | ✗ | B10 ✗ | idiom: cites `Nat.mul_le_mul_left` |
| C11 | 336 | `nf_firstStop_records` `hlasttake` | `(s.take m).getLastD false = s[m-1]` | ✗ | B11 ✗, D07 ✗ | idiom; contains K-chain (K3) |
| C12 | 345 | `nf_firstStop_records` `htake` | `m = s.length → s.take m = s` | ✗ | B12 ✗; D08 `List.take_length` | idiom: already cites `List.take_length` |
| C13 | 349 | `nf_firstStop_records` `hmlt` | `W*(r+1) < L` | ✗ | B13 ✗ | idiom: cites `Nat.mul_lt_mul_of_pos_left` |
| C14 | 355 | `nf_firstStop_records` `hniltake` | `0 < m → m ≤ s.length → s.take m ≠ []` | ✗ | B14 ✗, D06 ✗ | idiom (cites `List.ne_nil_of_length_pos`); contains K-chain (K4) |
| C15 | 359 | `nf_firstStop_records` `hz` | `(s.take m).length % W = 0` | ✗ | B15 ✗ | idiom; contains K-chain (K4) |
| C16 | 144, 152 | `nf_ctl_stop_iff` `hz'`, `hn'` | `(s++[b]).length % W = 0 → (s.length+1) % W = 0` | ✗ ✗ | B16 ✗ | idiom (`simpa` with `length_append`/`length_singleton`) |
| C17 | 502 | `nf_sweep_record` `hf` | `(fun i => r i.castSucc) = fun i => r ⟨i,_⟩` | `exact rfl` | – | definitional, no library lemma (optional `:= rfl`) |
| C18 | 509 | `nf_sweep_record` `harray` | last `Function.update` completes the record | ✗ | B18 ✗ | no library lemma |
| C19 | 684 | `nf_sweep_control_prefix` `hfalse` | `decide (a ≠ a) = false` | `decide_eq_false fun a => a rfl` | B19 same | idiom: the inline term *is* this |
| C20 | 1145 | `nf_bClear` `hdl` | `((R.drop i).length : ℤ) = R.length - i` | ✗ | B20 ✗ | idiom (`List.length_drop` + `Nat.cast_sub`) |
| C21 | 1584 | `nf_stream_cons` (private thm) | head/tail cells of `(rec::rs).flatMap ofFn` | – | B21, B21b, B21c ✗ | no library lemma |
| C22 | 1593, 1598 | `nf_stream_cons` `hlt` ×2 | index bounds in `ofFn rec ++ …` | ✗ ✗ | – | idiom (length rewrites + `omega`) |
| C23 | 1621 | `nf_flags_cons` (private thm) | end flags of `rec :: rs` | – | B23 ✗ | no library lemma |
| C24 | 2006 | `nf_blocks_write` `hin` | `min/max` interval membership off `y` | ✗ | B24 ✗ | no library lemma |
| C25 | 2064 | `nf_signType_bound` (private thm) | `-1 ≤ (m:ℤ) ∧ (m:ℤ) ≤ 1` | – | B25, B25a, B25b ✗ | no library lemma (Mathlib has `SignType.neg_one_le`/`le_one` only on `SignType`, no cast bound) |
| C26 | 2330 | `nf_stream_length` (private thm) | `(rs.flatMap ofFn).length = W * rs.length` | ✗ | B26, B26a ✗ | no Mathlib lemma; cites TCSlib `Turing.length_flatMap_uniform` (Rule 10-compliant) |
| C27 | 2864 | `nf_split` `hidx` | `r < n → p < W → W*r + p < W*n` | ✗ | B27/27a/27b ✗, D10 ✗ | no library lemma |
| **C28** | 2873 | `nf_split` bullet `rs ≠ []` | `0 < n → List.ofFn f ≠ []` | ✗ | B28 ✗, D02 ✗ (`exact?` does not contrapose) | **genuine G6** (`List.ofFn_eq_nil_iff`) |
| **C29** | 3006 | `nf_V_display` `hne` | `rs.length = w.length → w ≠ [] → rs ≠ []` | ✗ | B29 ✗; **D03 `List.ne_nil_of_length_pos h`** | **genuine G7** |
| C30 | 3016 | `nf_V_display` `hmap` | `rs.map (· 0) = w` | ✗ | – | idiom: `List.ext_getElem` with the TCSlib fact `nf_record_choice`, not a library statement |
| C31 | 3109 | `nf_forward` `hw₀len` | `t₀ ≤ w.length → (w.take t₀).length = t₀` | ✗ | B31 ✗; **D04 `List.length_take_of_le h`** | K-chain (K6) |
| **C32** | 3110 | `nf_forward` `hw₀ne` | `l.length = t₀ → 0 < t₀ → l ≠ []` | ✗ | B32 ✗; **D03** | **genuine G8** |
| C33 | 1327 | `nf_prefix_last` bullet | same statement as C18 | ✗ | – | no library lemma (in-file duplicate of C18, see notes) |
| C34 | 481 | `nf_sweep_prefix` bullet | one more `Function.update` extends the stored prefix | ✗ | B34 ✗ | no library lemma |
| **C36a** | 119–122 | `nf_ctl_position` bullet 1 | `a % (b+1) = b → (a+1) % (b+1) = 0` | – | B36a ✗; **D11 `Nat.succ_mod_succ_eq_zero_iff.mpr h`** | **genuine G1** |
| C36b | 123–127 | `nf_ctl_position` bullet 2 | `a % c + 1 < c → (a+1) % c = a % c + 1` | – | B36b ✗, D12 ✗ | idiom (`Nat.add_mod`/`Nat.mod_eq_of_lt` rewrites) |
| K | 263, 265, 284–285, 337–338, 357, 360, 371, 3109 | rw chains | `rw [List.length_take, Nat.min_eq_left h]` | – | **D04 `List.length_take_of_le h`** | **genuine rw-chain class K** |
| F | 141, 1338, 2949–2950 (+ split: 476/479, 501/507, 680/682, 1390–1391) | rw chains | `rw [List.foldl_append, List.foldl_cons, List.foldl_nil]` on `l ++ [x]` | – | **D13 `List.foldl_concat f b x xs`** | **genuine rw-chain class F** (split sites optional) |

## Genuine hits and tested replacements

All replacements below are in `NFLibC.lean` / `copyC.diff`. The elaboration result is exit 0 with no
errors and no warnings (`copyC.log` is empty apart from timing), identical to the baseline
(`base.log`).

| hit | line | inline proof (what it re-derives) | tested replacement |
|---|---|---|---|
| G1 | 119–122, `nf_ctl_position` bullet | `rw [Nat.add_mod, Nat.mod_eq_of_lt …, hm]`, `have he …`, `simp only [he, Nat.mod_self, …]`: re-proves `Nat.succ_mod_succ_eq_zero_iff` (→) | `simp only [Nat.succ_mod_succ_eq_zero_iff.mpr hm, Fin.val_zero]` |
| G2 | 268, `nf_display_firstStop` `hn` | 6-line `by_contra … Nat.mul_zero … omega`: re-proves `Nat.pos_of_mul_pos_left` (core proves it by `by_contra` too) | `have hn : 0 < i / (2 * N.k + 4) := Nat.pos_of_mul_pos_left (hipos.trans_eq he.symm)` |
| G3 | 274, `nf_display_firstStop` `hlt` | `(Nat.mul_lt_mul_left hW).mp` + exact-division `he`: re-proves `Nat.div_lt_of_lt_mul` | `have hlt : i / (2 * N.k + 4) < w.length :=`<br>`  Nat.div_lt_of_lt_mul (hi.trans_eq (nf_display_length N x w))` |
| G4 | 318, `nf_firstStop_records` `hlen` | `Nat.mod_add_div` + `rw [hmod, zero_add]`: re-proves `Nat.mul_div_cancel'` in its `% = 0` form | `have hlen : s.length = (2 * k + 4) * n :=`<br>`  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm` |
| G5 | 322, `nf_firstStop_records` `hn` | 6-line `by_contra`: re-proves `Nat.pos_of_mul_pos_left` | `have hn : 0 < n := Nat.pos_of_mul_pos_left (hspos.trans_eq hlen)` |
| G6 | 2873–2876, `nf_split` bullet | `congrArg List.length` + `length_ofFn`/`length_nil` + `omega`: re-proves `List.ofFn_eq_nil_iff` (→, contraposed) | `· exact mt List.ofFn_eq_nil_iff.mp hn.ne'` |
| G7 | 3006–3010, `nf_V_display` `hne` | `congrArg List.length` + `length_nil` + `eq_nil_of_length_eq_zero`: re-proves `List.ne_nil_of_length_pos` | `have hne : rs ≠ [] := List.ne_nil_of_length_pos (hrlen ▸ List.length_pos_iff.mpr hw)` |
| G8 | 3110–3114, `nf_forward` `hw₀ne` | `congrArg List.length` + `length_nil` + `omega`: re-proves `List.ne_nil_of_length_pos` | `have hw₀ne : w₀ ≠ [] := List.ne_nil_of_length_pos (by omega)` |

G4 is the borderline member. Its replacement chains two lemmas, because `exact?` finds no
single lemma in `% = 0` form (B08 ✗). It is included because the inline proof is the textbook
derivation of `Nat.mul_div_cancel'`, by the same argument that flagged round 2's `h0`. Note also
that the file already uses `List.ne_nil_of_length_pos` itself (lines 292, 356), so G7/G8 are
inconsistent with its own practice.

**Class K** (`rw [List.length_take, Nat.min_eq_left h]` is `rw [List.length_take_of_le h]`; core proves
`List.length_take_of_le` by `simp [Nat.min_eq_left h]`):

| site | tested replacement |
|---|---|
| 261–264 `hipos` (K1) | `have hipos : 0 < i := (List.length_pos_iff.mpr hne).trans_eq (List.length_take_of_le hi.le)` |
| 265 (K1) | `rw [List.length_take_of_le hi.le] at hm` |
| 284–286 (K2) | `rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take_of_le hi.le,`<br>`  List.getElem?_take_of_lt (by omega), hflag, Option.getD_some] at hb` |
| 337–339 `hlasttake` (K3) | `rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take_of_le hmle,`<br>`  List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hib, Option.getD_some]` |
| 355–358 `hniltake` (K4) | `have hniltake : s.take m ≠ [] :=`<br>`  List.ne_nil_of_length_pos (hmpos.trans_eq (List.length_take_of_le hmle).symm)` |
| 360 `hz` (K4) | `rw [List.length_take_of_le hmle]` |
| 371 `nf_display_prefix_length` (K5) | `rw [nf_display_length, List.length_take_of_le ht]` |
| 3109 `hw₀len` (K6) | `have hw₀len : w₀.length = t₀ := List.length_take_of_le (by omega)` |

**Class F** (`List.foldl_append, List.foldl_cons, List.foldl_nil` on `l ++ [x]` is Mathlib
`List.foldl_concat`, `Mathlib/Data/List/Basic.lean:725`, proved by
`simp only [List.foldl_append, List.foldl]`):

| site | tested replacement |
|---|---|
| 141 `nf_ctl_stop_iff` (F1) | `rw [List.foldl_concat, nf_ctlStep] at hp ⊢` |
| 1338 `nf_prefix_last` (F2) | `rw [List.ofFn_succ_last, List.foldl_concat] at h` |
| 2949–2950 `nf_vrun_of_ok` (F3) | `rw [List.take_succ_eq_append_getElem hlt, List.foldl_concat, ih,`<br>`  List.take_succ_eq_append_getElem (by rw [List.length_map]; exact hlt), …]` |
| optional, split sites: 476/479 (F4), 501/507 (F5a+F5b, together), 680/682 (F6), 1390–1391 (F7) | `List.foldl_append` becomes `List.foldl_concat`; drop the later `List.foldl_cons, List.foldl_nil` (see `copyC.diff`) |

The split sites interleave other steps (`simp only [Fin.coe_castSucc, …]`, `rw [ih …]`) between
the three rewrites. They are less clearly re-derivations, but they were converted and tested too,
so the maintainer can take all or none. Line 115 (`simp only [List.foldl_append, List.foldl_cons,
List.foldl_nil, List.length_append, …]`) is a simp set and was left alone.

## Excluded (one-liners) and other notes

* `obtain ⟨v, rfl⟩ : ∃ v, u = a + v := ⟨u - a, by omega⟩` occurs 13 times (lines 1108, 1259,
  1265, 1718, 2144, 2231, 2234, 2566, 2570, 2574, 2748, 2835, 2840). Its content is
  `Nat.exists_eq_add_of_le` (B38 found it). These are term one-liners and
  `Nat.exists_eq_add_of_le (by omega)` is no shorter, so they are not candidates.
* 2291 `hL' : (L : ℤ) = E - S + 1 := by rw [hL]; omega` is `Int.toNat_of_nonneg` (B35 found
  `Int.eq_ofNat_toNat.mpr`). It is an `omega` one-liner, and the lemma still needs `by omega` for
  nonnegativity, so it is excluded.
* 2046 `obtain ⟨z, hz | hz⟩ : ∃ z, q = p₀ + 2 * z ∨ q = p₀ + 2 * z + 1 := ⟨(q - p₀) / 2, by omega⟩`.
  B37 found no lemma; `Int.even_or_odd'` lacks the offset. It is a one-liner and is excluded.
* Out of scope (in-file duplication, not a library re-derivation): `nf_prefix_last` (1327–1336)
  re-proves the same `Function.update` statement as `nf_sweep_record`'s `harray` (509–520).
* `NFLibC.lean` is a test artifact, not a patch to land verbatim. It carries all F-sites, including
  the optional split ones; `copyC.diff` shows each change separately.

## Files

* `README.md`: this report. `copyC.diff`: the tested replacements as a unified diff against the source.
* `mk_copyA.py`, `mk_copyC.py`: copy generators (each asserts every old text occurs exactly once).
* `all_haves.txt`: the enumeration. `copyA_tags.tsv`, `copyB_tags.tsv`, `copyB2_tags.tsv`: probe line maps.
* `copyA.log`, `copyB.log`, `copyB2.log`, `copyC.log`, `base.log`: raw elaboration output.
* Scratch Lean (git-excluded): `wt-191/rvprobe/sweep/NFLibA.lean`, `NFLibB.lean`, `NFLibB2.lean`,
  `NFLibC.lean`, `NFLibBase.lean`.

## The maintainer's integration (2026-11-06)

- The sweep ran on a sub-agent of the cloud maintainer session, against `oleans-lzsa2`, and was
  reviewed by the maintainer. Its probe files are here as `.lean.txt` (`NFLibA`, `NFLibB`,
  `NFLibB2`); `NFLibC` is `dfc3e990`'s file with `copyC.diff` applied.
- `copyC.diff` was applied to #191's file as is (`patch -p0`; the result is `cmp`-identical to
  `NFLibC`). The in-file duplicate the sweep noted outside its scope, `nf_prefix_last` against
  `nf_sweep_record`'s `harray`, was then made one private, `nf_update_last`, cited by both. That is
  commit `49c4d0f7`.
- The result elaborates against `oleans-ldwa3` (the campaign after #196) with no output
  (`../elab/`), and `replay-lnf4` passes (`../merged-tree/`).
