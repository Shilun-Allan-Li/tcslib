# REPORT-fa: U9 (CarrySave, F5-F6) and U10 (Compare, F7-F8)

Worktree `/home/user/wt-fa` (detached at base 05999162), not committed. All 14 targets proved; 0 `sorry` in both files.

## 1. Files, sizes, final checks
| File | Lines base -> now | Max width | Final log | rc | errors | `declaration uses 'sorry'` |
|---|---|---|---|---|---|---|
| `TCSlib/Complexity/CircuitComplexity/FormulaArith/CarrySave.lean` | 297 -> 665 (+368) | 99 | `logs/CS-008.log` | 0 | 0 | 0 (no warnings at all) |
| `TCSlib/Complexity/CircuitComplexity/FormulaArith/Compare.lean` | 238 -> 556 (+318) | 100 | `logs/CMP-004.log` | 0 | 0 | 0 (no warnings at all) |

Order: CS-008 is the last CarrySave build (after its last edit), CMP-004 the last Compare build, after CS-008.
Sizes vs r3: U9 +368 (estimate 250-400); U10 +318 (estimate 150-250; about 75 lines are the private helper copies
that Compare cannot import from CarrySave, see section 7). `git diff` removes only `sorry` lines and sketch text.
Self-check (evidence only, not a substitute for the lead's seals): probes `probes/SealCS.lean`, `probes/SealCMP.lean`
(copies of the two files with `attribute [local irreducible]` on every foreign def used: `bitsVal`, `prefixVal`,
`carryBit`, `sumBit`, `Lit.eval`, `TreeCircuit.maxDepth/maxFaninL/const/and2/or2/xor2/xor3/maj3/balanced/neg`, and
for Compare also `FormulaArith.val/csaStep/csaLayer/csaLevels/csaReduce`; `TreeCircuit.eval/depth/maxFanin` are
already irreducible): `logs/SealCS-002.log`, `logs/SealCMP-002.log`, rc 0, 0 errors.

## 2. Targets and private helpers used
CarrySave (namespace `BoolCircuit.FormulaArith`):
- `csaStep_val`: yes. `val_eq_prefixVal_getD`, `prefixVal_eq_of_false`, `prefixVal_fullAdder`.
- `depth_csaStep_le`: yes. `depth_getD_le`, `maxDepth_le_of_forall`.
- `maxFaninL_csaStep_le`: yes. `maxFanin_getD_le`, `maxFaninL_le_of_forall`.
- `csaReduce_val`: yes. `sum_csaLayer`, `length_csaLayer`, `length_repeat_csaLayer`, `iterate_csaLevels_le_two`.
- `depth_csaReduce_le`: yes. `depth_csaLayer_le`, `mem_flatten_of_mem_getD`, `maxDepth_le_of_forall`.
- `maxFaninL_csaReduce_le`: yes. `maxFanin_csaLayer_le`, `mem_flatten_of_mem_getD`, `maxFaninL_le_of_forall`.
- `csaLevels_le`: yes. none (strong induction, `csaLevels_of_le_two`, `csaLevels_of_two_lt` twice, `k2 <= (k+2-1)/2`
  by `omega` for all k, `Nat.clog_pos`, `Nat.clog_mono_right`, `Nat.clog_of_two_le`).
Compare:
- `carryOut_eval`: yes. `eval_getD_const`, `carryBit_eq_true_iff`.
- `carryOut_eval_le`: yes. `val_eq_prefixVal_bitAt` (-> `prefixVal_eq_of_false`).
- `depth_carryOut_le`: yes. `depth_getD_le`, `maxDepth_le_of_forall`.
- `maxFanin_carryOut_le`: yes. `maxFanin_getD_le`, `maxFaninL_le_of_forall`.
- `geConst_eval`: yes. `val_eq_prefixVal_bitAt`, `eval_getD_const`, `prefixVal_testBit`.
- `depth_geConst_le`: yes. `maxDepth_le_of_forall`.
- `maxFanin_geConst_le`: yes. `maxFaninL_le_of_forall`.

## 3. Private helpers (all docstrings state the formula and say "Glue."; names grep-checked: 0 hits in TCSlib/, audits/)
CarrySave:
- `maxDepth_le_of_forall {cs} {d} (h : ∀ c ∈ cs, c.depth ≤ d) : TreeCircuit.maxDepth cs ≤ d` - Addendum A form;
  no public converse of `depth_le_maxDepth` in TCSlib (only private TreeDAG/TreeNCAC map variants).
- `maxFaninL_le_of_forall {cs} {d} (h : ∀ c ∈ cs, c.maxFanin ≤ d) : TreeCircuit.maxFaninL cs ≤ d` - same.
- `prefixVal_eq_of_false {f} {i m} (hle : i ≤ m) (h : ∀ j, i ≤ j → f j = false) : prefixVal f m = prefixVal f i`
  - Adder has only `prefixVal_congr` (same width); no padding lemma anywhere.
- `val_eq_prefixVal_getD x {U} {m} (hm : U.length ≤ m) : val x U = prefixVal (fun j => (U.getD j (const false)).eval x) m`
  - own-def glue (no such reader of `val`).
- `prefixVal_fullAdder {a b c s k} {L} (hs : ∀ j < L, s j = (a j ^^ b j ^^ c j)) (hk0 : k 0 = false)
  (hk : ∀ j < L, k (j + 1) = (a j && b j || c j && (a j ^^ b j))) :
  prefixVal a L + prefixVal b L + prefixVal c L = prefixVal s L + prefixVal k (L + 1)` - nearest is Adder.lean:405
  `prefixVal_add` (two-operand ripple form with `sumBit`/`carryBit`), not applicable to carry-save words.
- `depth_getD_le {U} {d} (h : ∀ c ∈ U, c.depth ≤ d) (hd : 1 ≤ d) (i) : (U.getD i (const false)).depth ≤ d` - glue.
- `maxFanin_getD_le {U} {d} (h : ∀ c ∈ U, c.maxFanin ≤ d) (i) : (U.getD i (const false)).maxFanin ≤ d` - glue.
- `sum_csaLayer x : ∀ Us, ((csaLayer Us).map (val x)).sum = (Us.map (val x)).sum` - own defs.
- `length_csaLayer : ∀ Us, (csaLayer Us).length = 2 * (Us.length / 3) + Us.length % 3` - own defs.
- `length_repeat_csaLayer Us : ∀ j, (Nat.repeat csaLayer j Us).length = (fun k => 2 * (k / 3) + k % 3)^[j] Us.length`
  - own defs; core has no `Nat.repeat` equation lemmas, so `show` steps + Mathlib `Function.iterate_succ_apply'`.
- `iterate_csaLevels_le_two (k) : (fun k => 2 * (k / 3) + k % 3)^[csaLevels k] k ≤ 2` - own defs.
- `mem_flatten_of_mem_getD {Vs} {i} {c} (h : c ∈ Vs.getD i []) : c ∈ Vs.flatten` - no `getD ∈` lemma in core/Mathlib
  (searched `getD_mem`, `mem_getD`); uses core `List.mem_flatten_of_mem`.
- `depth_csaLayer_le {d} (hd : 1 ≤ d) : ∀ Us, (∀ c ∈ Us.flatten, c.depth ≤ d) → ∀ c ∈ (csaLayer Us).flatten, c.depth ≤ d + 4`
  - own defs (has a sketch).
- `maxFanin_csaLayer_le {d} (hd : 2 ≤ d) : ∀ Us, (∀ c ∈ Us.flatten, c.maxFanin ≤ d) → ∀ c ∈ (csaLayer Us).flatten, c.maxFanin ≤ d`
  - own defs (has a sketch).
Compare:
- `maxDepth_le_of_forall`, `maxFaninL_le_of_forall`, `prefixVal_eq_of_false`, `depth_getD_le`, `maxFanin_getD_le`:
  same statements as in CarrySave (CarrySave's are private, so not visible here).
- `eval_getD_const x U j : (U.getD j (const false)).eval x = bitAt x U j` - own-def glue (`bitAt_eq`, `List.getD_map`, `const_eval`).
- `val_eq_prefixVal_bitAt x {U} {m} (hm : U.length ≤ m) : val x U = prefixVal (bitAt x U) m` - glue through `val_eq`.
- `carryBit_eq_true_iff A B b : carryBit A B b = true ↔ ∃ j < b, A j = true ∧ B j = true ∧ ∀ i, j < i → i < b → (A i || B i) = true`
  - no such lemma in TCSlib (only Adder's readers); has a sketch.
- `prefixVal_testBit c p : prefixVal c.testBit p = c % 2 ^ p` - BITS-LEMMA (section 7); core's `Nat.mod_two_pow_succ`
  is private; proof by `prefixVal_succ`, core `Nat.mod_pow_succ`, `Nat.toNat_testBit`.

## 4. Readers used (foreign lemmas), per target
- `csaStep_val`: `bitsVal_eq_prefixVal`, `prefixVal_congr`, `prefixVal_succ`, `prefixVal_zero`, `TreeCircuit.const_eval`,
  `xor3_eval`, `maj3_eval` (own: `val_eq`, `csaStep_eq`).
- `depth_csaStep_le`: `depth_le_maxDepth`, `depth_const`, `depth_xor3_le`, `depth_maj3_le`, `maxDepth_nil/_cons`.
- `maxFaninL_csaStep_le`: `maxFanin_le_maxFaninL`, `maxFanin_const`, `maxFanin_xor3_le`, `maxFanin_maj3_le`, `maxFaninL_nil/_cons`.
- `csaReduce_val`: `bitsVal_eq_prefixVal`, `prefixVal_zero` (+ the F5 value lemma; own `csaReduce_eq`,
  `csaLayer_cons_cons_cons`, `csaLayer_of_length_le_two`, `csaLevels_of_le_two/_two_lt`).
- `depth_csaReduce_le`: `depth_le_maxDepth`, `maxDepth_nil/_cons` (+ `depth_csaStep_le`).
- `maxFaninL_csaReduce_le`: `maxFanin_le_maxFaninL`, `maxFaninL_nil/_cons` (+ `maxFaninL_csaStep_le`).
- `csaLevels_le`: Mathlib `Nat.clog_pos`, `Nat.clog_mono_right`, `Nat.clog_of_two_le`.
- `carryOut_eval`: `TreeCircuit.balanced_eval`, `eval_node_false_iff`, `eval_node_true_iff`, `and2_eval`, `or2_eval`,
  `const_eval`, `carryBit_zero`, `carryBit_succ` (own `carryOut_eq`, `bitAt_eq`).
- `carryOut_eval_le`: `prefixVal_add`, `prefixVal_lt`, `val_eq` (CarrySave reader), `bitsVal_eq_prefixVal`,
  `prefixVal_congr`, `prefixVal_succ`.
- `depth_carryOut_le`: `depth_balanced_le`, `depth_and2_le`, `depth_or2_le`, `depth_le_maxDepth`, `depth_const`,
  `maxDepth_nil/_cons`; Mathlib `Nat.clog_mono_right`.
- `maxFanin_carryOut_le`: `maxFanin_balanced_le`, `maxFanin_and2_le`, `maxFanin_or2_le`, `maxFanin_le_maxFaninL`,
  `maxFanin_const`, `maxFaninL_nil/_cons`.
- `geConst_eval`: `csaStep_eq`, `csaStep_val`, `val_eq` (CarrySave), `const_eval`, `maj3_eval`, `prefixVal_add`,
  `prefixVal_lt`, `prefixVal_succ`, `prefixVal_zero`, `bitsVal_eq_prefixVal`, `prefixVal_congr`; core
  `Nat.mod_pow_succ`, `Nat.toNat_testBit`, `Nat.mod_eq_of_lt` (own `geConst_eq`, `constBits_eq`).
- `depth_geConst_le`: `depth_const`, `depth_le_maxDepth`, `depth_csaStep_le` (CarrySave target), `depth_carryOut_le`.
- `maxFanin_geConst_le`: `maxFanin_const`, `maxFanin_le_maxFaninL`, `maxFaninL_csaStep_le` (CarrySave target),
  `maxFanin_carryOut_le`.
Compare reads `val`/`csaStep` only through `val_eq`, `csaStep_eq` and the CarrySave targets (no unfold; checked by
the SealCMP probe, which seals `val`, `csaStep`, `csaLayer`, `csaLevels`, `csaReduce`).
Proved-modulo dependencies (frozen, `sorry` at the base, U8 F3): `const_eval`, `depth_const`, `maxFanin_const`,
`and2_eval`, `or2_eval`, `xor3_eval`, `maj3_eval`, `depth_and2_le`, `depth_or2_le`, `depth_xor3_le`, `depth_maj3_le`,
`maxFanin_and2_le`, `maxFanin_or2_le`, `maxFanin_xor3_le`, `maxFanin_maj3_le`. O1's `balanced_eval`,
`depth_balanced_le`, `maxFanin_balanced_le` are proved.
Core-definition reductions only in `rfl`/`show`/`change` steps (`Nat.repeat` in `show`/`change`/`rfl`; `Nat.iterate`
at `0` in `rfl`); Bool truth tables by `cases ... <;> rfl`/`decide`.

## 5. Refreshed sketches (old and new; also `sketches-CarrySave.json`, `sketches-Compare.json`)
Statement prose before `**Proof sketch.**` is byte-identical (only sketch lines and `sorry` lines are removed in the diff).

### CarrySave
**csaStep_val**

Old:
```
**Proof sketch.** Write every value through `val_eq` and `bitsVal_eq_prefixVal` as a
`prefixVal` of its bit sequence, extended to `L + 1` bits by `false` (`prefixVal_congr`; the
padding `const false` evaluates to `false` by `const_eval`).  Bit by bit, the full-adder
identity `a + b + c = (a ⊕ b ⊕ c) + 2 · maj(a, b, c)` holds by cases on three Booleans, with
`xor3_eval` and `maj3_eval` giving the values of `S_i` and `K_{i+1}`; summing it with weights
`2 ^ i` (induction on the number of bits, `prefixVal_succ`) gives the equation. -/
```
New:
```
**Proof sketch.** With `L = max |A| (max |B| |C|)`, `csaStep_eq` gives `S` (length `L`) and
`K` (length `L + 1`).  Every value is a `prefixVal` of its bits padded by `const false`, over
`L` bits for `A, B, C, S` and `L + 1` bits for `K` (`val_eq_prefixVal_getD`: `val_eq`,
`bitsVal_eq_prefixVal`, `prefixVal_congr`, `List.getD_map`, `const_eval`, and
`prefixVal_eq_of_false` for the padding).  Bit by bit, `S_i` is `xor3` and `K_{i+1}` is `maj3`
of the padded inputs (`xor3_eval`, `maj3_eval`) and `K_0 = false` (`const_eval`); the
full-adder identity `a + b + c = (a ⊕ b ⊕ c) + 2 · maj(a, b, c)` (cases on three Booleans),
summed with weights `2 ^ i` by induction on the number of bits (`prefixVal_succ`), gives the
equation (`prefixVal_fullAdder`). -/
```

**depth_csaStep_le**

Old:
```
**Proof sketch.** `csaStep_eq`.  Each padded input bit `A.getD i (const false)` has depth at
most `max 1 (maxDepth (A ++ B ++ C))` (`depth_le_maxDepth` for a member, `depth_const` for the
padding).  Then `depth_xor3_le` bounds every `S_i` by that plus `4`, `depth_maj3_le` every
`K_{i+1}` by that plus `3`, and `depth_const` gives `K_0` depth `1`; a list induction with
`maxDepth_cons`/`maxDepth_nil` (and `maxDepth` of an append) bounds the maximum. -/
```
New:
```
**Proof sketch.** `csaStep_eq`.  Each padded input bit `A.getD i (const false)` has depth at
most `max 1 (maxDepth (A ++ B ++ C))` (`depth_getD_le`: `depth_le_maxDepth` for a member,
`depth_const` for the padding).  Then `depth_xor3_le` bounds every `S_i` by that plus `4`,
`depth_maj3_le` every `K_{i+1}` by that plus `3`, and `depth_const` gives `K_0` depth `1`; a
bound on every member bounds the maximum (`maxDepth_le_of_forall`, by list induction with
`maxDepth_cons`/`maxDepth_nil`). -/
```

**maxFaninL_csaStep_le**

Old:
```
**Proof sketch.** `csaStep_eq`; each padded input bit has fan-in at most
`maxFaninL (A ++ B ++ C)` (`maxFanin_le_maxFaninL`, `maxFanin_const`), and
`maxFanin_xor3_le`, `maxFanin_maj3_le` bound every output bit; a list induction with
`maxFaninL_cons`/`maxFaninL_nil` bounds the maximum. -/
```
New:
```
**Proof sketch.** `csaStep_eq`; each padded input bit has fan-in at most
`maxFaninL (A ++ B ++ C)` (`maxFanin_getD_le`: `maxFanin_le_maxFaninL`, `maxFanin_const`), and
`maxFanin_xor3_le`, `maxFanin_maj3_le`, `maxFanin_const` bound every output bit; a bound on
every member bounds the maximum (`maxFaninL_le_of_forall`, by list induction with
`maxFaninL_cons`/`maxFaninL_nil`). -/
```

**csaReduce_val**

Old:
```
**Proof sketch.** (1) One layer keeps the total, `((csaLayer Us).map (val x)).sum =
(Us.map (val x)).sum`: induction along `csaLayer`'s cases (`csaLayer_cons_cons_cons`,
`csaLayer_of_length_le_two`) with `csaStep_val` for each triple.  (2) One layer sends length
`k` to `2 (k / 3) + k % 3` (same induction, `List.length_cons`).  (3) Induction on `k` along
`csaLevels_of_le_two`/`csaLevels_of_two_lt`: after `csaLevels k` layers at most two numbers are
left, with the original total.  (4) For a list of length at most two the total is
`getD 0 [] + getD 1 []`, as `val x [] = 0` (`val_eq`, `bitsVal` of `[]` is `0` by
`bitsVal_eq_prefixVal` and `prefixVal_zero`). -/
```
New:
```
**Proof sketch.** (1) One layer keeps the total, `((csaLayer Us).map (val x)).sum =
(Us.map (val x)).sum` (`sum_csaLayer`: recursion along `csaLayer`'s cases,
`csaLayer_cons_cons_cons`, with `csaStep_val` for each triple), hence so does every iterate
(induction on the number of layers, `Nat.repeat`).  (2) One layer sends length `k` to
`2 (k / 3) + k % 3` (`length_csaLayer`, the same recursion with `csaLayer_of_length_le_two`),
so `j` layers give the `j`-th iterate of that map (`length_repeat_csaLayer`).  (3) Induction on
`k` along `csaLevels_of_le_two`/`csaLevels_of_two_lt`: after `csaLevels k` steps of the map at
most two numbers are left (`iterate_csaLevels_le_two`).  (4) For a list of length at most two
the total is `getD 0 [] + getD 1 []`, as `val x [] = 0` (`val_eq`, `bitsVal` of `[]` is `0` by
`bitsVal_eq_prefixVal` and `prefixVal_zero`). -/
```

**depth_csaReduce_le**

Old:
```
**Proof sketch.** With `D = max 1 (maxDepth Us.flatten)`: one layer raises the bound by at
most `4` (`csaLayer`'s cases, `depth_csaStep_le` for each triple, the kept remainder
unchanged), so `j` layers give `D + 4 j` (induction on `j`, `Nat.repeat`); with
`j = csaLevels |Us|` the two read-off numbers are members (or `[]`) of the final list
(`List.getD`, `maxDepth_nil`). -/
```
New:
```
**Proof sketch.** With `D = max 1 (maxDepth Us.flatten)`: one layer raises a bound on the
depth of every formula by at most `4` (`depth_csaLayer_le`: `csaLayer`'s cases,
`depth_csaStep_le` for each triple, the kept remainder unchanged), so after `j` layers every
formula has depth `≤ D + 4 j` (induction on `j`, `Nat.repeat`); with `j = csaLevels |Us|` the
formulas of the two read-off numbers are formulas of the final list
(`mem_flatten_of_mem_getD`), and `maxDepth_le_of_forall` bounds the maximum. -/
```

**maxFaninL_csaReduce_le**

Old:
```
**Proof sketch.** As `depth_csaReduce_le`, with `maxFaninL_csaStep_le` for each triple: the
bound `max 2 (maxFaninL Us.flatten)` is kept by every layer. -/
```
New:
```
**Proof sketch.** As `depth_csaReduce_le`, with `maxFaninL_csaStep_le` for each triple: the
bound `max 2 (maxFaninL Us.flatten)` on every formula is kept by every layer
(`maxFanin_csaLayer_le`), and `maxFaninL_le_of_forall` bounds the maximum. -/
```

**csaLevels_le (tail of the sketch only; its first lines are unchanged)**

Old:
```
and `k₂ ≤ ⌈k / 2⌉` (by `omega` for `k ≥ 20`, from `k₂ ≤ (4k + 10) / 9`, and by cases below), so
`⌈log₂ k₂⌉ ≤ ⌈log₂ k⌉ - 1` (`Nat.clog_mono_right`, `Nat.clog_of_two_le`) and the induction
hypothesis closes it. -/
```
New:
```
and `k₂ ≤ ⌈k / 2⌉ = (k + 2 - 1) / 2` (by `omega`, for every `k > 2` with `k₁ > 2`), so
`⌈log₂ k₂⌉ + 1 ≤ ⌈log₂ k⌉` (`Nat.clog_mono_right`, `Nat.clog_of_two_le`) and the induction
hypothesis at `k₂ < k` closes it. -/
```

### Compare
**carryOut_eval**

Old:
```
**Proof sketch.** Induction on `b` for the unrolled carry: `carryBit A B (i + 1) =
(A_i ∧ B_i) ∨ ((A_i ⊕ B_i) ∧ carryBit A B i)` (reader of `carryBit` missing; see the census)
equals `(A_i ∧ B_i) ∨ ((A_i ∨ B_i) ∧ carryBit A B i)` by cases, and unrolling gives
`carryBit A B b = ∃ j < b, A_j ∧ B_j ∧ ∀ k, j < k < b → A_k ∨ B_k`.  On the formula side
`carryOut_eq`, `balanced_eval`, `eval_node_false`/`eval_node_true`, `and2_eval`, `or2_eval`,
and each padded bit evaluates to `bitAt x U j` (`bitAt_eq`, `const_eval` for the padding,
`List.getD_map`). -/
```
New:
```
**Proof sketch.** Induction on `b` for the unrolled carry: `carryBit A B (i + 1) =
(A_i ∧ B_i) ∨ ((A_i ⊕ B_i) ∧ carryBit A B i)` (`carryBit_zero`, `carryBit_succ`) equals
`(A_i ∧ B_i) ∨ ((A_i ∨ B_i) ∧ carryBit A B i)` by cases, and unrolling gives
`carryBit A B b = ∃ j < b, A_j ∧ B_j ∧ ∀ k, j < k < b → A_k ∨ B_k` (`carryBit_eq_true_iff`).
On the formula side `carryOut_eq`, `balanced_eval`, `eval_node_false_iff`/`eval_node_true_iff`,
`and2_eval`, `or2_eval`, and each padded bit evaluates to `bitAt x U j` (`eval_getD_const`:
`bitAt_eq`, `const_eval` for the padding, `List.getD_map`); the inner index `k` of disjunct `j`
is the bit `j + 1 + k`. -/
```

**carryOut_eval_le**

Old:
```
**Proof sketch.** `carryOut_eval`, then `prefixVal_add` (`Adder.lean:397`) at `b`:
`prefixVal A b + prefixVal B b = prefixVal (sumBit A B) b + 2 ^ b · carry`.  Here
`prefixVal (bitAt x U) b = val x U` (`val_eq`, `bitsVal_eq_prefixVal`, and `prefixVal_congr`
to extend from `|U|` to `b` bits by `false`), and `prefixVal (sumBit A B) b < 2 ^ b`
(`prefixVal_lt`), so the carry is `1` exactly when `2 ^ b ≤ val x U + val x W`. -/
```
New:
```
**Proof sketch.** `carryOut_eval`, then `prefixVal_add` (`Adder.lean:397`) at `b`:
`prefixVal A b + prefixVal B b = prefixVal (sumBit A B) b + 2 ^ b · carry`.  Here
`prefixVal (bitAt x U) b = val x U` (`val_eq_prefixVal_bitAt`: `val_eq`, `bitsVal_eq_prefixVal`,
`prefixVal_congr`, and `prefixVal_eq_of_false` to extend from `|U|` to `b` bits by `false`), and
`prefixVal (sumBit A B) b < 2 ^ b` (`prefixVal_lt`), so the carry is `1` exactly when
`2 ^ b ≤ val x U + val x W`. -/
```

**depth_carryOut_le**

Old:
```
**Proof sketch.** With `D = max 1 (maxDepth (U ++ W))`: every padded bit has depth `≤ D`
(`depth_le_maxDepth`, `depth_const`), so every `and2`/`or2` item has depth `≤ D + 1`
(`depth_and2_le`, `depth_or2_le`).  The inner list for `j < b` has `b - j ≤ b` items, so its
`balanced true` tree has depth `≤ D + 1 + ⌈log₂ b⌉ + 1` (`depth_balanced_le`,
`Nat.clog_mono_right`); the outer list has `b` items, so the outer `balanced false` tree adds
`⌈log₂ b⌉ + 1` more. -/
```
New:
```
**Proof sketch.** With `D = max 1 (maxDepth (U ++ W))`: every padded bit has depth `≤ D`
(`depth_getD_le`: `depth_le_maxDepth`, `depth_const`), so every `and2`/`or2` item has depth
`≤ D + 1` (`depth_and2_le`, `depth_or2_le`, `maxDepth_le_of_forall`).  The inner list for
`j < b` has `b - j ≤ b` items, so its `balanced true` tree has depth `≤ D + 1 + ⌈log₂ b⌉ + 1`
(`depth_balanced_le`, `Nat.clog_mono_right`); the outer list has `b` items, so the outer
`balanced false` tree adds `⌈log₂ b⌉ + 1` more (`depth_balanced_le`, `maxDepth_le_of_forall`). -/
```

**maxFanin_carryOut_le**

Old:
```
**Proof sketch.** `carryOut_eq`; `maxFanin_balanced_le` for both trees, `maxFanin_and2_le`,
`maxFanin_or2_le`, and each padded bit has fan-in `≤ maxFaninL (U ++ W)`
(`maxFanin_le_maxFaninL`, `maxFanin_const`); list inductions with `maxFaninL_cons`. -/
```
New:
```
**Proof sketch.** `carryOut_eq`; `maxFanin_balanced_le` for both trees, `maxFanin_and2_le`,
`maxFanin_or2_le`, and each padded bit has fan-in `≤ maxFaninL (U ++ W)` (`maxFanin_getD_le`:
`maxFanin_le_maxFaninL`, `maxFanin_const`); a bound on every member bounds each list's maximum
(`maxFaninL_le_of_forall`, by list induction with `maxFaninL_cons`). -/
```

**geConst_eval (from "`2 ^ p < c` both sides..." on; the earlier sketch lines are unchanged)**

Old:
```
`2 ^ p < c` both sides are constant (`const_eval`).  Otherwise
`T = 2 ^ p - c < 2 ^ p` and `val x (constBits p T) = T` (`constBits_eq`, `const_eval`,
`Nat.testBit` and `bitsVal`); `csaStep_val` gives `val S + val K = val U + val W + T`.  The
carry word `K` has `p + 1` bits, but its top bit is `maj3` of the padding of `U`, `W` (both
`const false`, as `|U|, |W| ≤ p - 1`) and a bit of `T`, so it is `false` (`csaStep_eq`,
`maj3_eval`); hence `carryOut_eval` and `prefixVal_add` give the carry into position `p` as
`decide (2 ^ p ≤ val S + val K)` (`carryOut_eval_le` applied to `K` without its top bit), which
is `decide (c ≤ val x U + val x W)`. -/
```
New:
```
`2 ^ p < c` both sides are constant (`const_eval`).  Otherwise
`T = 2 ^ p - c < 2 ^ p` and `val x (constBits p T) = T` (`val_eq_prefixVal_bitAt`,
`constBits_eq`, `const_eval`, and `prefixVal c.testBit p = c % 2 ^ p` by `prefixVal_testBit`:
`prefixVal_succ`, `Nat.mod_pow_succ`, `Nat.toNat_testBit`); `csaStep_val` gives
`val S + val K = val U + val W + T`, with `|S| = p` and `|K| = p + 1` (`csaStep_eq`).  The top
bit of the carry word `K` is `maj3` of the padding of `U`, `W` (both `const false`, as
`|U|, |W| ≤ p - 1`) and a bit of `T`, so it is `false` (`csaStep_eq`, `maj3_eval`) and
`val K = prefixVal (bitAt x K) p`; hence `carryOut_eval` and `prefixVal_add` at `p`, with
`prefixVal_lt` for the sum bits, give the carry into position `p` as
`decide (2 ^ p ≤ val S + val K)`, which is `decide (c ≤ val x U + val x W)`. -/
```

**depth_geConst_le**

Old:
```
**Proof sketch.** `geConst_eq`.  The constant cases have depth `1` (`depth_const`).  Otherwise,
with `D = max 1 (maxDepth (U ++ W))`: the constant bits have depth `1` (`constBits_eq`,
`depth_const`), so `depth_csaStep_le` bounds both words by `D + 4`, and `depth_carryOut_le` at
`p = max |U| |W| + 1` adds `2⌈log₂ p⌉ + 3`. -/
```
New:
```
**Proof sketch.** `geConst_eq`.  The constant cases have depth `1` (`depth_const`).  Otherwise,
with `D = max 1 (maxDepth (U ++ W))`: the constant bits have depth `1` (`constBits_eq`,
`depth_const`), so `maxDepth (U ++ W ++ constBits …) ≤ D` (`maxDepth_le_of_forall`),
`depth_csaStep_le` bounds both words by `D + 4`, and `depth_carryOut_le` at
`p = max |U| |W| + 1` adds `2⌈log₂ p⌉ + 3`. -/
```

**maxFanin_geConst_le**

Old:
```
**Proof sketch.** `geConst_eq`; `maxFanin_const` for the constant cases, otherwise
`maxFanin_carryOut_le` and `maxFaninL_csaStep_le` (the constant bits have fan-in `0`). -/
```
New:
```
**Proof sketch.** `geConst_eq`; `maxFanin_const` for the constant cases, otherwise
`maxFanin_carryOut_le` and `maxFaninL_csaStep_le` (the constant bits have fan-in `0`, so
`maxFaninL (U ++ W ++ constBits …) ≤ maxFaninL (U ++ W)` by `maxFaninL_le_of_forall`). -/
```

## 6. Imports added
None.

## 7. Overlaps, promotion requests, scope requests, false targets
- **BITS-LEMMA** (for the lead's `maskedConst`): no reusable TCSlib/Mathlib/core lemma. `AdderLanguage.lean:72`
  `bitsVal_natToBits` would need a reader for the elements of `natToBits` (none; Rule 10). Core
  `Nat.mod_two_pow_succ` is private. Route used: private `prefixVal_testBit` (`prefixVal c.testBit p = c % 2 ^ p`,
  3-line induction with `prefixVal_succ`, `Nat.mod_pow_succ`, `Nat.toNat_testBit`, `Nat.mul_comm`), then
  `val_eq_prefixVal_bitAt` + `prefixVal_congr` (bit `j < p` of `constBits p T` is `T.testBit j` by `eval_getD_const`,
  `constBits_eq`, `List.getD_eq_getElem`, `List.getElem_map`, `List.getElem_range`, `const_eval`).
- Promotion requests: (a) Addendum A family `maxDepth_le_of_forall`, `maxFaninL_le_of_forall` -> `Basic.lean`
  (nearest: private `TreeNCAC.lean:215/226`, `TreeDAG.lean:407/420`); (b) `prefixVal_eq_of_false`,
  `prefixVal_testBit`, `carryBit_eq_true_iff`, `prefixVal_fullAdder` -> `Adder.lean` (nearest `prefixVal_congr`
  Adder.lean:110, `prefixVal_add` :405); (c) `depth_getD_le`, `maxFanin_getD_le` -> `Combinators.lean` (padding by
  `const false`); (d) a public reader `val x U = prefixVal (fun j => (U.getD j (const false)).eval x) m` for
  `m ≥ |U|` in `CarrySave.lean` would remove Compare's `val_eq_prefixVal_bitAt`/`eval_getD_const` overlap.
- Disclosed duplication between my two (mutually foreign) files: `maxDepth_le_of_forall`, `maxFaninL_le_of_forall`,
  `prefixVal_eq_of_false`, `depth_getD_le`, `maxFanin_getD_le` appear privately in both with identical statements;
  `val_eq_prefixVal_getD` (CarrySave) and `val_eq_prefixVal_bitAt` (Compare) state the same padded-value fact in two
  shapes. Private helpers cannot be shared across modules; one promotion (above) removes all copies.
- Scope requests: none. Targets believed false: none.

## 8. Resources
Peak RSS 1,906,512 kB (SealCMP-002); 16 Lean runs (CS-001..008, CMP-001..004, SealCS-001..002, SealCMP-001..002),
each about 2-7 s. Evidence: `/home/user/w6/evidence/subagents/fa/` (`logs/`, `probes/`, `snapshots/`, `searches.md`,
`progress.md`, `sketches-*.json`).
