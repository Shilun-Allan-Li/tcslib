/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Yao reduction machine

The machine of [PS10, Algorithm 38.5] behind Theorem 35.1 (`weak_to_strong` in
`TCSlib.Cryptography.Asymptotic.OneWay`, which imports this file): given an inverter `A'` of the
direct product `f'(x₁, …, x_m) = (f(x₁), …, f(x_m))`, the reduction repeats `T + 1` times —
sample a position `i ← [m]` by rejection (D10), sample `m` fresh inputs, evaluate `f` on them,
plant the challenge `y` at block `i`, call `A'`, and test whether block `i` of the answer is a
preimage of `y` — and returns the first success. The machine is
`Complexity.polyTimeComputable_iterateFind` on the raw input `⟨⟨⟨1^n, y⟩, ⟨α', 1^k⟩⟩, r⟩` (the
coins `r` are consumed one round at a time), its round is an FP composition of the
sub-machines of `TCSlib.Cryptography.Asymptotic.OneWayLemmas`, and the main theorem
`exists_yaoReduction` identifies its inverter with the concrete `OneWay.yaoInverter` of
[Gar26, Figure 2.2] up to the statistical term `(T + 1)·2^{-n}` of the rejection-sampled
positions (`statClose_pi`, `statClose_rejectionSample`).

The file is generic over the lengths `inLen`, `outLen`, the block count `m`, the round count
`T` (all `PolyExpr`) and the function `f` with its evaluator `Fe`; `OneWay.lean` instantiates it
with a `FunFamily`.

## Main definitions

* `TCSlib.Cryptography.OneWay.blocksE` — the block bijection (the `blocks` of `OneWay.lean`).
* `TCSlib.Cryptography.OneWay.kkOf` — the trial length `⌊log₂ m⌋ + 1` of the position sampler.
* `TCSlib.Cryptography.OneWay.YaoMachine.Data`, `YaoMachine.acc`, `YaoMachine.ans`,
  `YaoMachine.g`, `YaoMachine.yaoRaw'` — the round of Algorithm 38.5 and the repeated machine.
* `TCSlib.Cryptography.OneWay.yaoB` — the total inverter of the direct product read off `A'`.

## Main results

* `TCSlib.Cryptography.OneWay.ofFn_blocksE_symm_update` — planting a block is splicing.
* `TCSlib.Cryptography.OneWay.exists_yaoReduction` — the reduction machine and its bound.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4: Theorem 35.1 and Algorithm 38.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography.OneWay

open Complexity Turing Finset

/-! ### The block bijection -/

/-- A string of `q·ℓ` bits as `q` consecutive blocks of `ℓ` bits (block `i` occupies the
positions `ℓ·i, …, ℓ·i + ℓ - 1`); the `FunFamily.blocks` of `OneWay.lean`, repeated here
because this file is imported by it. -/
def blocksE (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- Block `i`, position `j` of `x` is position `ℓ·i + j`. -/
theorem blocksE_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    blocksE q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl

/-- The inverse of `blocksE` reads block `k.divNat`, position `k.modNat`. -/
theorem blocksE_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (k : Fin (q * ℓ)) :
    (blocksE q ℓ).symm t k = t k.divNat k.modNat := rfl

/-- The encoding of a tuple of blocks is the concatenation of the encodings of the blocks. -/
theorem ofFn_blocksE_symm (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) :
    List.ofFn ((blocksE q ℓ).symm t) = (List.ofFn fun i => List.ofFn (t i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  rw [blocksE_symm_apply]
  have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (by rintro rfl; exact j.elim0)
  congr 1
  · refine Fin.ext ?_
    simp only [Fin.coe_divNat]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hℓ, Nat.div_eq_of_lt j.2, zero_add]
  · refine Fin.ext ?_
    simp only [Fin.coe_modNat]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-- **Planting is splicing:** the encoding of the tuple `t` with block `p` replaced by `v` is the
encoding of `t` with the `ℓ` bits after `p·ℓ` replaced by the encoding of `v`
[PS10, Algorithm 38.5, "`(f(x₁), …, y, …, f(x_m))`"].

**Proof sketch.** Both sides have length `q·ℓ`; compare position `i`: below `p·ℓ` and from
`p·ℓ + ℓ` on, both read block `i / ℓ ≠ p` of `t` (`Function.update_of_ne`), and in between both
read position `i - p·ℓ` of `v` (`Function.update_self`, `Nat.div_add_mod`). -/
theorem ofFn_blocksE_symm_update {q ℓ : ℕ} (t : Fin q → Fin ℓ → Bool) (p : Fin q)
    (v : Fin ℓ → Bool) :
    List.ofFn ((blocksE q ℓ).symm (Function.update t p v)) =
      (List.ofFn ((blocksE q ℓ).symm t)).take (p * ℓ) ++ List.ofFn v ++
        (List.ofFn ((blocksE q ℓ).symm t)).drop (p * ℓ + ℓ) := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · refine List.ext_getElem (by simp) fun i h₁ _ => ?_
    simp at h₁
  have hle : p * ℓ + ℓ ≤ q * ℓ := by
    have : (p + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ p.2
    rwa [Nat.add_mul, Nat.one_mul] at this
  have hLlen : (List.ofFn ((blocksE q ℓ).symm t)).length = q * ℓ := List.length_ofFn
  have hT : ((List.ofFn ((blocksE q ℓ).symm t)).take (p * ℓ)).length = p * ℓ := by
    rw [List.length_take, hLlen]; omega
  have hV : (List.ofFn v).length = ℓ := List.length_ofFn
  have hTV : ((List.ofFn ((blocksE q ℓ).symm t)).take (p * ℓ) ++ List.ofFn v).length = p * ℓ + ℓ := by
    rw [List.length_append, hT, hV]
  refine List.ext_getElem ?_ fun i h₁ h₂ => ?_
  · simp only [List.length_append, List.length_drop, hT, hV, hLlen, List.length_ofFn]
    omega
  rw [List.getElem_ofFn, blocksE_symm_apply, Function.update_apply]
  rw [List.length_ofFn] at h₁
  have hdiv : ((⟨i, h₁⟩ : Fin (q * ℓ)).divNat : ℕ) = i / ℓ := Fin.coe_divNat _
  have hmod : ((⟨i, h₁⟩ : Fin (q * ℓ)).modNat : ℕ) = i % ℓ := Fin.coe_modNat _
  have hdm := Nat.div_add_mod i ℓ
  rcases lt_or_ge i (p * ℓ) with hA | hA
  · -- below the planted block: block `i / ℓ < p`
    have hq : i / ℓ < p := (Nat.div_lt_iff_lt_mul hℓ).2 hA
    rw [if_neg (by rw [Fin.ext_iff, hdiv]; omega)]
    rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega),
      List.getElem_take, List.getElem_ofFn, blocksE_symm_apply]
  · rcases lt_or_ge i (p * ℓ + ℓ) with hB | hB
    · -- the planted block
      have hlo : p ≤ i / ℓ := (Nat.le_div_iff_mul_le hℓ).2 hA
      have hhi : i / ℓ < p + 1 :=
        (Nat.div_lt_iff_lt_mul hℓ).2 (by rw [Nat.add_mul, Nat.one_mul]; exact hB)
      have hq : i / ℓ = p := by omega
      rw [if_pos (by rw [Fin.ext_iff, hdiv]; exact hq)]
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega),
        List.getElem_ofFn]
      congr 1
      rw [Fin.ext_iff, hmod]
      simp only [hT]
      rw [hq, Nat.mul_comm] at hdm
      omega
    · -- above the planted block: block `i / ℓ > p`
      have hq : p + 1 ≤ i / ℓ :=
        (Nat.le_div_iff_mul_le hℓ).2 (by rw [Nat.add_mul, Nat.one_mul]; exact hB)
      rw [if_neg (by rw [Fin.ext_iff, hdiv]; omega)]
      rw [List.getElem_append_right (by omega), List.getElem_drop, List.getElem_ofFn,
        blocksE_symm_apply]
      congr 1 <;> (apply Fin.ext; simp only [Fin.coe_divNat, Fin.coe_modNat]; congr 1; omega)

/-! ### The trial length of the position sampler -/

/-- The trial length `⌊log₂ m⌋ + 1` of the rejection sampler of `i ← [m]`: the least `k` with
`m < 2^k`, so that `2^k ≤ 2m` and every trial succeeds with probability at least `1/2`
(D10, [PS10, Theorem 35.1]). -/
def kkOf (M : ℕ) : ℕ := Nat.log 2 M + 1

/-- The trial length is positive. -/
theorem kkOf_pos (M : ℕ) : 0 < kkOf M := Nat.succ_pos _

/-- `m < 2^{kkOf m}`. -/
theorem lt_two_pow_kkOf (M : ℕ) : M < 2 ^ kkOf M := Nat.lt_pow_succ_log_self one_lt_two M

/-- `2^{kkOf m} ≤ 2m` for `0 < m`. -/
theorem two_pow_kkOf_le (M : ℕ) (hM : 0 < M) : 2 ^ kkOf M ≤ 2 * M := by
  rw [kkOf, pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hM.ne')

/-- `kkOf m ≤ m` for `0 < m`. -/
theorem kkOf_le (M : ℕ) (hM : 0 < M) : kkOf M ≤ M :=
  Nat.log_lt_of_lt_pow hM.ne' Nat.lt_two_pow_self

/-- `kkOf m ≤ m + 1`. -/
theorem kkOf_le_succ (M : ℕ) : kkOf M ≤ M + 1 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [kkOf]
  · exact (kkOf_le M hM).trans (Nat.le_succ M)

/-! ### The round of Algorithm 38.5 -/

namespace YaoMachine

/-- The data of the reduction: the evaluator `Fe` of `f` (on `⟨1^n, x⟩`), the blockwise
evaluator `F'` (`exists_prodEval`), the position sampler `Pm` (`exists_posMachine`), the
lengths `inLen`, `outLen`, the block count `m` and the given inverter `A'`. -/
structure Data where
  /-- The evaluator of `f` on `⟨1^n, x⟩`. -/
  Fe : List Bool → List Bool
  /-- The blockwise evaluator on `⟨1^n, x₁ ⋯ x_m⟩`. -/
  F' : List Bool → List Bool
  /-- The position sampler on `⟨⟨1^k, 1^m⟩, trials⟩`. -/
  Pm : List Bool → List Bool
  /-- The input length of `f`. -/
  inLen : PolyExpr
  /-- The output length of `f`. -/
  outLen : PolyExpr
  /-- The number of blocks. -/
  m : PolyExpr
  /-- The given inverter of the direct product. -/
  A' : NUPPT

variable (D : Data)

/-- The coins of one round: `n·m(n)` position bits (of which `n·k` are read), `m(n)·inLen(n)`
bits of fresh inputs, and the coins of `A'`. -/
def ρP : PolyExpr := .add (.mul .var D.m) (.add (.mul D.m D.inLen) D.A'.coins)

/-- The advice of `A'`, read off the advice slot `⟨α', 1^k⟩`. -/
def alpha1 (w : List Bool) : List Bool := pairFstD (NUPPT.inAdvice w)

/-- The trial length `1^k`, read off the advice slot `⟨α', 1^k⟩`. -/
def ukk (w : List Bool) : List Bool := pairSndD (NUPPT.inAdvice w)

/-- The block count in unary, `1^{m(n)}`. -/
def uM (w : List Bool) : List Bool := List.replicate (D.m.eval (NUPPT.inParam w).length) true

/-- The coins of the current round: the first `ρ(n)` remaining coins. -/
def rc (w : List Bool) : List Bool :=
  (NUPPT.inCoins w).take ((ρP D).eval (NUPPT.inParam w).length)

/-- `1^{n·k}`: the number of position bits read. -/
def nkk (w : List Bool) : List Bool :=
  List.replicate ((NUPPT.inParam w).length * (ukk w).length) true

/-- The position bits of the round. -/
def posBits (w : List Bool) : List Bool := (rc D w).take (nkk w).length

/-- The sampled position in unary, `1^i`. -/
def ipos (w : List Bool) : List Bool :=
  D.Pm (pairEncode (pairEncode (ukk w) (uM D w)) (posBits D w))

/-- The fresh inputs `x₁ ⋯ x_m` of the round. -/
def xs (w : List Bool) : List Bool :=
  ((rc D w).drop ((PolyExpr.mul .var D.m).eval (NUPPT.inParam w).length)).take
    ((PolyExpr.mul D.m D.inLen).eval (NUPPT.inParam w).length)

/-- The coins handed to `A'`. -/
def rcoins (w : List Bool) : List Bool :=
  (rc D w).drop ((PolyExpr.add (.mul .var D.m) (.mul D.m D.inLen)).eval (NUPPT.inParam w).length)

/-- The tuple `f(x₁) ⋯ f(x_m)`. -/
def ys (w : List Bool) : List Bool := D.F' (pairEncode (NUPPT.inParam w) (xs D w))

/-- `1^{outLen(n)}`. -/
def uOut (w : List Bool) : List Bool := List.replicate (D.outLen.eval (NUPPT.inParam w).length) true

/-- `1^{i·outLen(n)}`: the offset of block `i` of the tuple. -/
def off (w : List Bool) : List Bool :=
  List.replicate ((ipos D w).length * (uOut D w).length) true

/-- The planted tuple `(f(x₁), …, y, …, f(x_m))`. -/
def planted (w : List Bool) : List Bool :=
  (ys D w).take (off D w).length ++ NUPPT.inArg w ++ (ys D w).drop (off D w ++ uOut D w).length

/-- The answer of `A'` on the planted tuple. -/
def zOut (w : List Bool) : List Bool :=
  D.A'.output (NUPPT.layout (NUPPT.inParam w) (planted D w) (alpha1 w) (rcoins D w))

/-- `1^{inLen(n)}`. -/
def uIn (w : List Bool) : List Bool := List.replicate (D.inLen.eval (NUPPT.inParam w).length) true

/-- `1^{i·inLen(n)}`: the offset of block `i` of the answer. -/
def offIn (w : List Bool) : List Bool :=
  List.replicate ((ipos D w).length * (uIn D w).length) true

/-- Block `i` of the answer, padded with `true` to `inLen(n)` bits. -/
def ans (w : List Bool) : List Bool :=
  ((zOut D w).drop (offIn D w).length ++ uIn D w).take (D.inLen.eval (NUPPT.inParam w).length)

/-- The test `f(z_i) = y`. -/
def test (w : List Bool) : Bool :=
  decide (D.Fe (pairEncode (NUPPT.inParam w) (ans D w)) = NUPPT.inArg w)

/-- The acceptance test of a round: a full round of coins remains and the test succeeds. -/
def acc (w : List Bool) : Bool :=
  decide ((ρP D).eval (NUPPT.inParam w).length ≤ (NUPPT.inCoins w).length) && test D w

/-- The step: drop one round of coins. -/
def g (w : List Bool) : List Bool :=
  pairEncode (pairFstD w) ((NUPPT.inCoins w).drop ((ρP D).eval (NUPPT.inParam w).length))

/-- The repeated machine: `T(|x|) + 1` rounds, the answer of the first successful one. -/
def yaoRaw (T : PolyExpr) (x : List Bool) : List Bool :=
  match (List.range (T.eval x.length + 1)).find? (fun i => acc D ((g D)^[i] x)) with
  | some i => ans D ((g D)^[i] x)
  | none => []

/-- The repeated machine with the default answer `1^{inLen(n)}` on exhaustion. -/
def yaoRaw' (T : PolyExpr) (x : List Bool) : List Bool :=
  if yaoRaw D T x = [] then uIn D x else yaoRaw D T x

section Poly

variable {D}
variable (hFe : PolyTimeComputable D.Fe) (hF' : PolyTimeComputable D.F') (hPm : PolyTimeComputable D.Pm)

/-- The advice of `A'` is polynomial-time. -/
theorem alpha1_poly : PolyTimeComputable alpha1 :=
  polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice

/-- The trial length is polynomial-time. -/
theorem ukk_poly : PolyTimeComputable ukk :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice

/-- The unary block count is polynomial-time. -/
theorem uM_poly : PolyTimeComputable (uM D) :=
  StateLoop.unaryPoly_comp D.m NUPPT.polyTimeComputable_inParam

/-- The round coins are polynomial-time. -/
theorem rc_poly : PolyTimeComputable (rc D) := by
  convert (polyTimeComputable_pairTakePoly (ρP D)).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins) using 1
  funext w
  simp [rc]

/-- `1^{n·k}` is polynomial-time. -/
theorem nkk_poly : PolyTimeComputable nkk := by
  convert polyTimeComputable_unaryMulPair.comp
    (NUPPT.polyTimeComputable_inParam.pairEncode ukk_poly) using 1
  funext w
  simp [nkk]

/-- The position bits are polynomial-time. -/
theorem posBits_poly : PolyTimeComputable (posBits D) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (nkk_poly.pairEncode (rc_poly (D := D))) using 1
  funext w
  simp [posBits]

include hPm in
/-- The position is polynomial-time. -/
theorem ipos_poly : PolyTimeComputable (ipos D) :=
  hPm.comp ((ukk_poly.pairEncode uM_poly).pairEncode posBits_poly)

/-- The fresh inputs are polynomial-time. -/
theorem xs_poly : PolyTimeComputable (xs D) := by
  convert (polyTimeComputable_pairTakePoly (.mul D.m D.inLen)).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairDropPoly (.mul .var D.m)).comp
        (NUPPT.polyTimeComputable_inParam.pairEncode (rc_poly (D := D))))) using 1
  funext w
  simp [xs]

/-- The coins handed to `A'` are polynomial-time. -/
theorem rcoins_poly : PolyTimeComputable (rcoins D) := by
  convert (polyTimeComputable_pairDropPoly (.add (.mul .var D.m) (.mul D.m D.inLen))).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode (rc_poly (D := D))) using 1
  funext w
  simp [rcoins]

include hF' in
/-- The tuple is polynomial-time. -/
theorem ys_poly : PolyTimeComputable (ys D) :=
  hF'.comp (NUPPT.polyTimeComputable_inParam.pairEncode xs_poly)

/-- `1^{outLen(n)}` is polynomial-time. -/
theorem uOut_poly : PolyTimeComputable (uOut D) :=
  StateLoop.unaryPoly_comp D.outLen NUPPT.polyTimeComputable_inParam

include hPm in
/-- The offset is polynomial-time. -/
theorem off_poly : PolyTimeComputable (off D) := by
  convert polyTimeComputable_unaryMulPair.comp
    ((ipos_poly hPm).pairEncode (uOut_poly (D := D))) using 1
  funext w
  simp [off]

include hF' hPm in
/-- The planted tuple is polynomial-time. -/
theorem planted_poly : PolyTimeComputable (planted D) := by
  convert (((polyTimeComputable_pairTakePoly .var).comp
      ((off_poly hPm).pairEncode (ys_poly hF'))).append NUPPT.polyTimeComputable_inArg).append
    ((polyTimeComputable_pairDropPoly .var).comp
      (((off_poly hPm).append (uOut_poly (D := D))).pairEncode (ys_poly hF'))) using 1
  funext w
  simp [planted]

include hF' hPm in
/-- The answer of `A'` is polynomial-time. -/
theorem zOut_poly : PolyTimeComputable (zOut D) :=
  D.A'.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam (planted_poly hF' hPm)
      alpha1_poly rcoins_poly)

/-- `1^{inLen(n)}` is polynomial-time. -/
theorem uIn_poly : PolyTimeComputable (uIn D) :=
  StateLoop.unaryPoly_comp D.inLen NUPPT.polyTimeComputable_inParam

include hPm in
/-- The answer offset is polynomial-time. -/
theorem offIn_poly : PolyTimeComputable (offIn D) := by
  convert polyTimeComputable_unaryMulPair.comp
    ((ipos_poly hPm).pairEncode (uIn_poly (D := D))) using 1
  funext w
  simp [offIn]

include hF' hPm in
/-- The padded answer block is polynomial-time. -/
theorem ans_poly : PolyTimeComputable (ans D) := by
  convert (polyTimeComputable_pairTakePoly D.inLen).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (((polyTimeComputable_pairDropPoly .var).comp
        ((offIn_poly hPm).pairEncode (zOut_poly hF' hPm))).append (uIn_poly (D := D)))) using 1
  funext w
  simp [ans]

include hFe hF' hPm in
/-- The test is polynomial-time (`Complexity.polyTimeComputable_pairEq`). -/
theorem test_poly : PolyTimeComputable fun w => [test D w] := by
  convert polyTimeComputable_pairEq.comp
    ((hFe.comp (NUPPT.polyTimeComputable_inParam.pairEncode (ans_poly hF' hPm))).pairEncode
      NUPPT.polyTimeComputable_inArg) using 1
  funext w
  simp [test]

include hFe hF' hPm in
/-- The acceptance test is polynomial-time. -/
theorem acc_poly : PolyTimeComputable fun w => [acc D w] := by
  convert polyTimeComputable_and
    (StateLoop.lenLe_comp NUPPT.polyTimeComputable_inCoins
      (StateLoop.unaryPoly_comp (ρP D) NUPPT.polyTimeComputable_inParam))
    (test_poly hFe hF' hPm) using 1
  funext w
  simp [acc]

/-- The step is polynomial-time. -/
theorem g_poly : PolyTimeComputable (g D) := by
  convert polyTimeComputable_pairFstD.pairEncode ((polyTimeComputable_pairDropPoly (ρP D)).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins)) using 1
  funext w
  simp [g]

/-- The orbit of every word under the step stays within `|w| + 2`. -/
theorem length_g_iterate_le (w : List Bool) (i : ℕ) : ((g D)^[i] w).length ≤ w.length + 2 := by
  have key : ∀ i, ((g D)^[i] w).length ≤ max w.length 2 := by
    intro i
    induction i with
    | zero => exact le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      refine (PosLoop.length_pairEncode_pairFstD_le _ _
        (by rw [List.length_drop]; exact Nat.sub_le _ _)).trans ?_
      exact max_le ih (le_max_right _ _)
  exact (key i).trans (by omega)

include hFe hF' hPm in
/-- The repeated machine is polynomial-time (`Complexity.polyTimeComputable_iterateFind`). -/
theorem yaoRaw_poly (T : PolyExpr) : PolyTimeComputable (yaoRaw D T) :=
  polyTimeComputable_iterateFind g_poly (acc_poly hFe hF' hPm) (ans_poly hF' hPm) T
    (.add .var (.const 2)) fun w i _ => by simpa using length_g_iterate_le w i

include hFe hF' hPm in
/-- The repeated machine with default is polynomial-time. -/
theorem yaoRaw'_poly (T : PolyExpr) : PolyTimeComputable (yaoRaw' D T) := by
  convert polyTimeComputable_ite (StateLoop.isNil_poly.comp (yaoRaw_poly hFe hF' hPm T))
    (uIn_poly (D := D)) (yaoRaw_poly hFe hF' hPm T) using 1
  funext w
  simp [yaoRaw']

end Poly

/-- The orbit on a raw input: after `i` rounds, `i·ρ(n)` coins have been dropped. -/
theorem iterate_g_layout (u y α r : List Bool) (i : ℕ) :
    (g D)^[i] (NUPPT.layout u y α r) =
      NUPPT.layout u y α (r.drop (i * (ρP D).eval u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [g, NUPPT.layout, NUPPT.inCoins, NUPPT.inParam, pairFstD_pairEncode,
      pairSndD_pairEncode, List.drop_drop]
    congr 2
    ring

end YaoMachine

/-! ### The typed coins of a round -/

/-- The coins of one round as a triple: `n·m` position bits, `m·k` bits of fresh inputs, and the
`c` coins of `A'`. -/
def roundEquiv (n M k c : ℕ) :
    (Fin (n * M) → Bool) × ((Fin (M * k) → Bool) × (Fin c → Bool)) ≃
      (Fin (n * M + (M * k + c)) → Bool) :=
  (Equiv.prodCongr (Equiv.refl _) (Fin.appendEquiv (M * k) c)).trans
    (Fin.appendEquiv (n * M) (M * k + c))

/-- The encoding of a round's coins is the concatenation of the three parts. -/
theorem ofFn_roundEquiv (n M k c : ℕ) (a : Fin (n * M) → Bool) (b : Fin (M * k) → Bool)
    (c' : Fin c → Bool) :
    List.ofFn (roundEquiv n M k c (a, (b, c'))) = List.ofFn a ++ (List.ofFn b ++ List.ofFn c') := by
  show List.ofFn (Fin.append a (Fin.append b c')) = _
  simp only [List.ofFn_fin_append]

/-- The `n` trials of `kk` bits read from the first `n·kk` position bits. -/
def pbOf {n M kk : ℕ} (h : n * kk ≤ n * M) (a : Fin (n * M) → Bool) : Fin n → Fin kk → Bool :=
  fun t j => a (Fin.castLE h (finProdFinEquiv (t, j)))

/-- The rejection-sampled position (`0` on failure). -/
def posOf {n M kk : ℕ} (hM : 0 < M) (h : n * kk ≤ n * M) (a : Fin (n * M) → Bool) : Fin M :=
  (rejectionSample M kk n (pbOf h a)).getD ⟨0, hM⟩

/-- Reading the trials pushes uniform position bits to uniform trials (a restriction to the
first `n·kk` coordinates followed by the block bijection).

**Proof sketch.** The restriction is the first projection of the bijection
`(Fin (n·m) → Bool) ≃ (Fin (n·kk) → Bool) × (Fin (n·m − n·kk) → Bool)` (`Fin.appendEquiv`,
`finCongr`), which pushes uniform to uniform (`HardcoreBit.pushesUniform_fst`); the block
bijection is a bijection. -/
theorem pushesUniform_pbOf {n M kk : ℕ} (h : n * kk ≤ n * M) :
    HardcoreBit.PushesUniform (pbOf (M := M) h) := by
  have hsum : n * M = n * kk + (n * M - n * kk) := by omega
  let e₁ : (Fin (n * M) → Bool) ≃ (Fin (n * kk) → Bool) × (Fin (n * M - n * kk) → Bool) :=
    (Equiv.arrowCongr (finCongr hsum) (Equiv.refl Bool)).trans (Fin.appendEquiv _ _).symm
  have h₁ : HardcoreBit.PushesUniform fun a : Fin (n * M) → Bool => (e₁ a).1 :=
    (HardcoreBit.pushesUniform_equiv e₁).comp HardcoreBit.pushesUniform_fst
  have h₂ := h₁.comp (HardcoreBit.pushesUniform_equiv (blocksE n kk))
  convert h₂ using 1

/-- The typed coins of a round read off the raw round coins: the position by rejection, the
fresh inputs as `m` blocks of `k` bits, and the coins of `A'`. -/
def roundSample (n M k c kk : ℕ) (hM : 0 < M) (h : n * kk ≤ n * M)
    (rc : Fin (n * M + (M * k + c)) → Bool) : Fin M × (Fin M → Fin k → Bool) × (Fin c → Bool) :=
  (posOf hM h ((roundEquiv n M k c).symm rc).1,
    blocksE M k ((roundEquiv n M k c).symm rc).2.1, ((roundEquiv n M k c).symm rc).2.2)

/-- The typed coins of a round are within `(1 − m/2^{kk})^n` of uniform
(`statClose_rejectionSample` for the position, bijections for the rest). -/
theorem statClose_roundSample (n M k c kk : ℕ) (hM : 0 < M) (hMk : M ≤ 2 ^ kk)
    (h : n * kk ≤ n * M) :
    StatClose (roundSample n M k c kk hM h) id ((1 - (M : ℝ) / 2 ^ kk) ^ n + 0) := by
  have hpos : StatClose (posOf (n := n) (kk := kk) hM h) (id : Fin M → Fin M)
      ((1 - (M : ℝ) / 2 ^ kk) ^ n) :=
    (statClose_rejectionSample M kk n hM hMk ⟨0, hM⟩).comp_pushesUniform (pushesUniform_pbOf h)
  have hbij : StatClose (Equiv.prodCongr (blocksE M k) (Equiv.refl (Fin c → Bool)))
      (id : (Fin M → Fin k → Bool) × (Fin c → Bool) → _) 0 :=
    statClose_of_pushesUniform (HardcoreBit.pushesUniform_equiv _)
  have hprod := (hpos.prod hbij).comp_equiv_left (roundEquiv n M k c).symm
  convert hprod using 1

/-- The total inverter of the direct product read off `A'`: on the tuple `ys` with coins `r`,
block `j` of `A'`'s answer, padded with `true` to `inLen(n)` bits (`padTrue`); when the answer
has the right length this is exactly `A'`'s inverse, so it inverts at least as often as `A'`
[PS10, Algorithm 38.5, "`z_i`"]. -/
def yaoB (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ) :
    (Fin (m.eval n) → Fin (outLen.eval n) → Bool) → A'.Coins n →
      (Fin (m.eval n) → Fin (inLen.eval n) → Bool) :=
  fun ys r j => padTrue (inLen.eval n)
    ((A'.runAt n (List.ofFn ((blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop
      (j * inLen.eval n))

namespace YaoMachine

variable (D : Data)

/-- The advice of the reduction: `⟨A'.advice n, 1^{kkOf (m n)}⟩`. -/
def adv (n : ℕ) : List Bool :=
  pairEncode (D.A'.advice n) (List.replicate (kkOf (D.m.eval n)) true)

/-- The advice bound `2·adv' + 2 + (m + 1)`. -/
def advP : PolyExpr := .add (.add (.mul (.const 2) D.A'.adv) (.const 2)) (.add D.m (.const 1))

/-- The advice is bounded by `advP`. -/
theorem adv_length (n : ℕ) : (adv D n).length ≤ (advP D).eval n := by
  simp only [adv, advP, length_pairEncode, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const]
  have := D.A'.advice_length n
  have := kkOf_le_succ (D.m.eval n)
  omega

/-- The number of coins of a round, `ρ(n) = n·m + (m·inLen + coins_{A'})`, in the form of
`roundEquiv`. -/
theorem ρP_eval (n : ℕ) :
    (ρP D).eval n = n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n) := rfl

/-- `n·kkOf m ≤ n·m` for `0 < m`. -/
theorem nkk_le (n M : ℕ) (hM : 0 < M) : n * kkOf M ≤ n * M := Nat.mul_le_mul_left n (kkOf_le M hM)

section Round

variable {D}
variable (n : ℕ) (hM : 0 < D.m.eval n)
  (f : (Fin (D.inLen.eval n) → Bool) → (Fin (D.outLen.eval n) → Bool))
  (hFe : ∀ a : Fin (D.inLen.eval n) → Bool,
    D.Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (f a))
  (hF' : ∀ x : Fin (D.m.eval n * D.inLen.eval n) → Bool,
    D.F' (pairEncode (List.replicate n true) (List.ofFn x)) =
      (List.ofFn fun i : Fin (D.m.eval n) => D.Fe (pairEncode (List.replicate n true)
        (List.ofFn fun j : Fin (D.inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten)
  (hPm : ∀ pb' : Fin (n * kkOf (D.m.eval n)) → Bool,
    D.Pm (pairEncode (pairEncode (List.replicate (kkOf (D.m.eval n)) true)
      (List.replicate (D.m.eval n) true)) (List.ofFn pb')) =
      List.replicate ((rejectionSample (D.m.eval n) (kkOf (D.m.eval n)) n
        fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true)
  (y : Fin (D.outLen.eval n) → Bool)
  (rc : Fin ((ρP D).eval n) → Bool)
  (rest' : List Bool)

include hFe hF' hPm in
/-- **The round identity:** on the state word of a round whose coins start with `rc`, the padded
answer block is the encoding of `OneWay.yaoTry` on the typed coins `roundSample rc`.

**Proof sketch.** Unfold the FP round on the layout: the projections return the slots, the
coin cuts return the three parts of `rc` (`ofFn_roundEquiv`, `List.take_left'`,
`List.drop_left'`), the position sampler returns `1^i` (`hPm`, `ofFn_castLE_eq_take`), the
blockwise evaluator returns the tuple `(f(x₁), …, f(x_m))` (`hF'`, `hFe`, `ofFn_blocksE_symm`),
planting is splicing (`ofFn_blocksE_symm_update`), `A'.output` on the layout is `A'.runAt`, and
the padded block is `padTrue` (`ofFn_padTrue`). -/
theorem ans_layout :
    ans D (NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn rc ++ rest')) =
      List.ofFn (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y
        (roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (kkOf (D.m.eval n)) hM
          (nkk_le n _ hM) rc)) := by
  obtain ⟨⟨a, b, c'⟩, rfl⟩ : ∃ p, roundEquiv n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) p = rc :=
    ⟨_, Equiv.apply_symm_apply _ rc⟩
  simp only [roundSample, Equiv.symm_apply_apply]
  set w := NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n)
    (List.ofFn (roundEquiv n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (a, b, c')) ++ rest')
    with hw
  have hu : NUPPT.inParam w = List.replicate n true := by simp [hw]
  have hy : NUPPT.inArg w = List.ofFn y := by simp [hw]
  have hα : NUPPT.inAdvice w = adv D n := by simp [hw]
  have hcoins : NUPPT.inCoins w =
      List.ofFn (roundEquiv n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (a, b, c')) ++ rest' := by
    simp [hw]
  have halpha : alpha1 w = D.A'.advice n := by simp [alpha1, hα, adv]
  have hukk : ukk w = List.replicate (kkOf (D.m.eval n)) true := by simp [ukk, hα, adv]
  have huM : uM D w = List.replicate (D.m.eval n) true := by simp [uM, hu]
  have hrc : rc D w = List.ofFn a ++ (List.ofFn b ++ List.ofFn c') := by
    simp only [YaoMachine.rc, hcoins, hu, List.length_replicate, ρP_eval]
    rw [List.take_left' (by simp), ofFn_roundEquiv]
  have hnkk : nkk w = List.replicate (n * kkOf (D.m.eval n)) true := by
    simp [nkk, hu, hukk]
  have hposBits : posBits D w =
      List.ofFn fun j : Fin (n * kkOf (D.m.eval n)) => a (Fin.castLE (nkk_le n _ hM) j) := by
    simp only [posBits, hrc, hnkk, List.length_replicate]
    rw [List.take_append_of_le_length (by simpa using nkk_le n _ hM), ← ofFn_castLE_eq_take]
  have hipos : ipos D w = List.replicate (posOf hM (nkk_le n _ hM) a).val true := by
    simp only [ipos, hukk, huM, hposBits]
    exact hPm _
  have hxs : xs D w = List.ofFn b := by
    simp only [xs, hrc, hu, PolyExpr.eval_mul, PolyExpr.eval_var, List.length_replicate]
    rw [List.drop_left' (by simp), List.take_left' (by simp)]
  have hrcoins : rcoins D w = List.ofFn c' := by
    simp only [rcoins, hrc, hu, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var,
      List.length_replicate]
    rw [← List.append_assoc, List.drop_left' (by simp)]
  have hys : ys D w = List.ofFn ((blocksE (D.m.eval n) (D.outLen.eval n)).symm
      (prodFun f (D.m.eval n) (blocksE (D.m.eval n) (D.inLen.eval n) b))) := by
    simp only [ys, hu, hxs]
    rw [hF' b, ofFn_blocksE_symm]
    congr 2
    funext i
    rw [hFe]
    rfl
  have huOut : uOut D w = List.replicate (D.outLen.eval n) true := by simp [uOut, hu]
  have hoff : off D w = List.replicate ((posOf hM (nkk_le n _ hM) a).val * D.outLen.eval n) true := by
    simp [off, hipos, huOut]
  have hplanted : planted D w = List.ofFn ((blocksE (D.m.eval n) (D.outLen.eval n)).symm
      (Function.update (prodFun f (D.m.eval n) (blocksE (D.m.eval n) (D.inLen.eval n) b))
        (posOf hM (nkk_le n _ hM) a) y)) := by
    rw [ofFn_blocksE_symm_update]
    simp only [planted, hoff, huOut, hys, hy, List.length_replicate, List.length_append]
  have hz : zOut D w = D.A'.runAt n (List.ofFn ((blocksE (D.m.eval n) (D.outLen.eval n)).symm
      (Function.update (prodFun f (D.m.eval n) (blocksE (D.m.eval n) (D.inLen.eval n) b))
        (posOf hM (nkk_le n _ hM) a) y))) c' := by
    simp only [zOut, hu, hplanted, halpha, hrcoins]
    rfl
  have huIn : uIn D w = List.replicate (D.inLen.eval n) true := by simp [uIn, hu]
  have hoffIn : offIn D w =
      List.replicate ((posOf hM (nkk_le n _ hM) a).val * D.inLen.eval n) true := by
    simp [offIn, hipos, huIn]
  simp only [ans, hoffIn, huIn, hz, hu, List.length_replicate]
  rw [yaoTry]
  simp only [yaoB]
  rw [ofFn_padTrue]

include hFe hF' hPm in
/-- **The round test:** on the state word of a round, the test is `f(z_i) = y`. -/
theorem test_layout :
    test D (NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn rc ++ rest')) =
      decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y
        (roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (kkOf (D.m.eval n)) hM
          (nkk_le n _ hM) rc)) = y) := by
  rw [test, ans_layout n hM f hFe hF' hPm y rc rest']
  simp only [NUPPT.inParam_layout, NUPPT.inArg_layout]
  rw [hFe]
  simp [List.ofFn_injective.eq_iff]

end Round

end YaoMachine

/-- `OneWay.yaoInverter` returns the first successful try, found by `List.find?`
(`foldr_ite_eq_find?`). -/
theorem yaoInverter_eq_find? {α β ρ : Type*} [DecidableEq β] {q : ℕ} (inst : Inhabited α)
    (f : α → β) (B : (Fin q → β) → ρ → (Fin q → α)) (T : ℕ) (y : β)
    (cs : Fin T → Fin q × (Fin q → α) × ρ) :
    @yaoInverter α β ρ _ q inst f B T y cs =
      ((List.finRange T).find? (fun t => decide (f (yaoTry f B y (cs t)) = y))).elim
        (@default α inst) (fun t => yaoTry f B y (cs t)) := by
  unfold yaoInverter
  have h := foldr_ite_eq_find? (fun t => f (yaoTry f B y (cs t)) = y)
    (fun t => yaoTry f B y (cs t)) (@default α inst) (List.finRange T)
  convert h

namespace YaoMachine

variable (D : Data)

section Loop

variable {D}
variable (T : PolyExpr) (n : ℕ) (hM : 0 < D.m.eval n)

/-- The typed coins of all `T(n) + 1` rounds, read off the coin string. -/
def sampleAll (r : Fin ((T.eval n + 1) * (ρP D).eval n) → Bool) :
    Fin (T.eval n + 1) →
      Fin (D.m.eval n) × (Fin (D.m.eval n) → Fin (D.inLen.eval n) → Bool) × D.A'.Coins n :=
  fun i => roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n) (kkOf (D.m.eval n)) hM
    (nkk_le n _ hM) (blocksE (T.eval n + 1) ((ρP D).eval n) r i)

/-- **The coins of all rounds are close to uniform:** within `(T(n) + 1)·(1 − m/2^{kk})^n`
(`statClose_roundSample`, `statClose_pi`, the block bijection on the coin string). -/
theorem statClose_sampleAll :
    StatClose (sampleAll T n hM) id
      (((T.eval n + 1 : ℕ) : ℝ) * ((1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n + 0)) :=
  (statClose_pi (statClose_roundSample n (D.m.eval n) (D.inLen.eval n) (D.A'.coinLen n)
    (kkOf (D.m.eval n)) hM (lt_two_pow_kkOf _).le (nkk_le n _ hM)) (T.eval n + 1)).comp_equiv_left
    (blocksE (T.eval n + 1) ((ρP D).eval n))

variable (hn : 1 ≤ n)
  (f : (Fin (D.inLen.eval n) → Bool) → (Fin (D.outLen.eval n) → Bool))
  (hFe : ∀ a : Fin (D.inLen.eval n) → Bool,
    D.Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (f a))
  (hF' : ∀ x : Fin (D.m.eval n * D.inLen.eval n) → Bool,
    D.F' (pairEncode (List.replicate n true) (List.ofFn x)) =
      (List.ofFn fun i : Fin (D.m.eval n) => D.Fe (pairEncode (List.replicate n true)
        (List.ofFn fun j : Fin (D.inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten)
  (hPm : ∀ pb' : Fin (n * kkOf (D.m.eval n)) → Bool,
    D.Pm (pairEncode (pairEncode (List.replicate (kkOf (D.m.eval n)) true)
      (List.replicate (D.m.eval n) true)) (List.ofFn pb')) =
      List.replicate ((rejectionSample (D.m.eval n) (kkOf (D.m.eval n)) n
        fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true)

include hn hFe hF' hPm in
/-- **The loop identity:** on the raw input `⟨⟨⟨1^n, y⟩, ⟨α', 1^k⟩⟩, r⟩` the repeated machine
returns the encoding of `OneWay.yaoInverter` with the default `1^{inLen(n)}` on the typed coins
`sampleAll r`.

**Proof sketch.** Round `i` runs on the layout with the first `i·ρ(n)` coins dropped
(`iterate_g_layout`); for `i ≤ T(n)` the remaining coins start with block `i` of `r`
(`ofFn_block_eq_take_drop`), so the round test is `f(z_i) = y` (`test_layout`) and the payload is
`yaoTry` on `sampleAll r i` (`ans_layout`); from round `T(n) + 1` on no coins remain and the test
fails. The loop's `find?` over `List.range (T(|x|) + 1) ⊇ [0, T(n)]` is the `find?` over
`finRange (T(n) + 1)` (`find?_range_eq_map_find?_finRange`), which is `yaoInverter`
(`yaoInverter_eq_find?`); on exhaustion both return `1^{inLen(n)}`. -/
theorem yaoRaw'_layout (y : Fin (D.outLen.eval n) → Bool)
    (r : Fin ((T.eval n + 1) * (ρP D).eval n) → Bool) :
    yaoRaw' D T (NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn r)) =
      List.ofFn (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ f (yaoB D.inLen D.outLen D.m D.A' n)
        (T.eval n + 1) y (sampleAll T n hM r)) := by
  set x₀ := NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n) (List.ofFn r) with hx₀
  have hρpos : 0 < (ρP D).eval n := by
    rw [ρP_eval]
    have := Nat.mul_pos hn hM
    omega
  have hstate : ∀ i, (g D)^[i] x₀ = NUPPT.layout (List.replicate n true) (List.ofFn y) (adv D n)
      ((List.ofFn r).drop (i * (ρP D).eval n)) := by
    intro i
    rw [hx₀, iterate_g_layout]
    simp only [List.length_replicate]
  have hblock : ∀ (i : ℕ) (h : i < T.eval n + 1), (List.ofFn r).drop (i * (ρP D).eval n) =
      List.ofFn (blocksE (T.eval n + 1) ((ρP D).eval n) r ⟨i, h⟩) ++
        ((List.ofFn r).drop (i * (ρP D).eval n)).drop ((ρP D).eval n) := by
    intro i h
    conv_lhs => rw [← List.take_append_drop ((ρP D).eval n) ((List.ofFn r).drop (i * (ρP D).eval n))]
    congr 1
    exact (ofFn_block_eq_take_drop r ⟨i, h⟩).symm
  have hacc : ∀ i : ℕ, acc D ((g D)^[i] x₀) =
      if h : i < T.eval n + 1 then
        decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r ⟨i, h⟩)) = y)
      else false := by
    intro i
    rw [hstate]
    split_ifs with h
    · rw [hblock i h]
      unfold acc
      rw [test_layout n hM f hFe hF' hPm y _ _]
      simp only [NUPPT.inParam_layout, NUPPT.inCoins_layout, List.length_replicate,
        List.length_append, List.length_ofFn]
      simp [sampleAll]
    · have hdrop : (List.ofFn r).drop (i * (ρP D).eval n) = [] := by
        apply List.drop_eq_nil_of_le
        rw [List.length_ofFn]
        exact Nat.mul_le_mul_right _ (not_lt.1 h)
      rw [hdrop]
      unfold acc
      simp only [NUPPT.inParam_layout, NUPPT.inCoins_layout, List.length_replicate,
        List.length_nil]
      simp [hρpos.ne']
  have hout : ∀ i : Fin (T.eval n + 1), ans D ((g D)^[i] x₀) =
      List.ofFn (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r i)) := by
    intro i
    rw [hstate, hblock i.1 i.2]
    exact ans_layout n hM f hFe hF' hPm y _ _
  have hR : T.eval n + 1 ≤ T.eval x₀.length + 1 := by
    have : n ≤ x₀.length := by
      simp only [hx₀, NUPPT.layout, length_pairEncode, List.length_replicate]
      omega
    exact Nat.succ_le_succ (T.eval_mono this)
  have hfind := find?_range_eq_map_find?_finRange hR
    (fun t : Fin (T.eval n + 1) =>
      decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r t)) = y))
    (fun i => acc D ((g D)^[i] x₀))
    (fun t h => by show acc D ((g D)^[t] x₀) = _; rw [hacc, dif_pos h])
    (fun t h => by show acc D ((g D)^[t] x₀) = _; rw [hacc, dif_neg (not_lt.2 h)])
  rw [yaoInverter_eq_find? ⟨fun _ => true⟩]
  unfold yaoRaw' yaoRaw
  rw [hfind]
  have huIn : uIn D x₀ = List.replicate (D.inLen.eval n) true := by simp [uIn, hx₀]
  cases hf : (List.finRange (T.eval n + 1)).find? fun t =>
      decide (f (yaoTry f (yaoB D.inLen D.outLen D.m D.A' n) y (sampleAll T n hM r t)) = y) with
  | none =>
    simp only [Option.map_none, Option.elim_none]
    simp [huIn, List.ofFn_const]
  | some t =>
    simp only [Option.map_some, Option.elim_some]
    rw [hout t]
    split_ifs with h0
    · have hk : D.inLen.eval n = 0 := by simpa using congrArg List.length h0
      rw [huIn, h0, hk]
      rfl
    · rfl

end Loop

end YaoMachine

/-- **The Yao reduction machine** [PS10, Algorithm 38.5]: for lengths `inLen`, `outLen`, a block
count `m` (positive at every `n ≥ 1`), a round count `T`, a function `f` with a polynomial-time
evaluator `Fe` on `⟨1^n, x⟩`, and any `NUPPT` `A'`, there is an `NUPPT` `A` whose inversion
probability against `f` at every `n ≥ 1` is at least that of the concrete
`OneWay.yaoInverter (f n) (yaoB … n) (T(n) + 1)` [Gar26, Figure 2.2] minus the statistical
term `(T(n) + 1)·2^{-n}` of the rejection-sampled positions (D10).

**Proof sketch.** `A := NUPPT.ofPolyTime` of `YaoMachine.yaoRaw'` (polynomial-time by
`YaoMachine.yaoRaw'_poly`, from `exists_prodEval`, `exists_posMachine` and
`Complexity.polyTimeComputable_iterateFind`) with coins `(T + 1)·ρ`, `ρ = n·m + m·inLen + coins_{A'}`,
and advice `⟨A'.advice n, 1^{kkOf (m n)}⟩` (bounded by `YaoMachine.advP`). At `n ≥ 1`,
`YaoMachine.yaoRaw'_layout` identifies `A`'s inverter with `some (yaoInverter … y (sampleAll r))`
(`decodeFin_ofFn`), so `A`'s inversion probability is the success probability of `yaoInverter`
on the sampled coins; `YaoMachine.statClose_sampleAll` and `StatClose.abs_uprob_sub_le_prod`
move it to uniform coins at the cost of `(T + 1)·(1 − m/2^{kk})^n ≤ (T + 1)·2^{-n}`
(`uprob_rejectionSample_none_le_half_pow`). -/
theorem exists_yaoReduction (inLen outLen m T : PolyExpr)
    (f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool))
    {Fe : List Bool → List Bool} (hFe : PolyTimeComputable Fe)
    (hFe_spec : ∀ n (a : Fin (inLen.eval n) → Bool),
      Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (f n a))
    (A' : NUPPT) (hm : ∀ n, 1 ≤ n → 0 < m.eval n) :
    ∃ A : NUPPT, ∀ n, 1 ≤ n →
      invProb (f n) (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1)) - (T.eval n + 1) * (1 / 2 : ℝ) ^ n ≤
        invProbOpt (f n) (A.inverter n (inLen.eval n) (outLen.eval n)) := by
  obtain ⟨F', hF', hF'spec⟩ := exists_prodEval hFe inLen m
  obtain ⟨Pm, hPm, hPmspec⟩ := exists_posMachine
  let D : YaoMachine.Data := ⟨Fe, F', Pm, inLen, outLen, m, A'⟩
  let A : NUPPT := NUPPT.ofPolyTime (YaoMachine.yaoRaw'_poly (D := D) hFe hF' hPm T)
    (.mul (.add T (.const 1)) (YaoMachine.ρP D)) (YaoMachine.advP D) (YaoMachine.adv D)
    (YaoMachine.adv_length D)
  refine ⟨A, fun n hn => ?_⟩
  have hM : 0 < D.m.eval n := hm n hn
  have hPm' : ∀ pb' : Fin (n * kkOf (D.m.eval n)) → Bool,
      D.Pm (pairEncode (pairEncode (List.replicate (kkOf (D.m.eval n)) true)
        (List.replicate (D.m.eval n) true)) (List.ofFn pb')) =
        List.replicate ((rejectionSample (D.m.eval n) (kkOf (D.m.eval n)) n
          fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true :=
    fun pb' => hPmspec (D.m.eval n) (kkOf (D.m.eval n)) n hM (kkOf_pos _) (two_pow_kkOf_le _ hM) pb'
  -- the functional identity
  have hrun : ∀ (y : Fin (outLen.eval n) → Bool) (r : A.Coins n),
      A.runAt n (List.ofFn y) r =
        List.ofFn (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) y (YaoMachine.sampleAll T n hM r)) := by
    intro y r
    rw [NUPPT.runAt_eq]
    show (NUPPT.ofPolyTime _ _ _ _ _).runAtL n _ _ = _
    rw [NUPPT.runAtL_ofPolyTime]
    exact YaoMachine.yaoRaw'_layout T n hM hn (f n) (hFe_spec n) (hF'spec n) hPm' y r
  have hinv : ∀ (y : Fin (outLen.eval n) → Bool) (r : A.Coins n),
      A.inverter n (inLen.eval n) (outLen.eval n) y r =
        some (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) y (YaoMachine.sampleAll T n hM r)) := by
    intro y r
    simp only [NUPPT.inverter, hrun, decodeFin_ofFn]
  -- the statistical switch
  have hS := YaoMachine.statClose_sampleAll T n hM
  have hδ : (1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n ≤ (1 / 2 : ℝ) ^ n := by
    have h1 := uprob_rejectionSample_none (D.m.eval n) (kkOf (D.m.eval n)) n hM
      (lt_two_pow_kkOf _).le
    have h2 := uprob_rejectionSample_none_le_half_pow (D.m.eval n) (kkOf (D.m.eval n)) n hM
      (lt_two_pow_kkOf _).le (two_pow_kkOf_le _ hM)
    rwa [h1] at h2
  have hS' : StatClose (fun r : A.Coins n => YaoMachine.sampleAll T n hM r) id
      (((T.eval n + 1 : ℕ) : ℝ) * ((1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n + 0)) := hS
  have key := hS'.abs_uprob_sub_le_prod fun cs (x : Fin (inLen.eval n) → Bool) =>
    f n (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
      (T.eval n + 1) (f n x) cs) = f n x
  have hL : invProbOpt (f n) (A.inverter n (inLen.eval n) (outLen.eval n)) =
      uprob fun z : A.Coins n × (Fin (inLen.eval n) → Bool) =>
        f n (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) (f n z.2) (YaoMachine.sampleAll T n hM z.1)) = f n z.2 := by
    unfold invProbOpt
    rw [← uprob_comp_equiv (Equiv.prodComm (A.Coins n) (Fin (inLen.eval n) → Bool))]
    congr 1
    funext z
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hinv, Option.some.injEq,
      exists_eq_left']
  have hR : invProb (f n) (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
      (T.eval n + 1)) =
      uprob fun z : (Fin (T.eval n + 1) →
          Fin (m.eval n) × (Fin (m.eval n) → Fin (inLen.eval n) → Bool) × A'.Coins n) ×
          (Fin (inLen.eval n) → Bool) =>
        f n (@yaoInverter _ _ _ _ _ ⟨fun _ => true⟩ (f n) (yaoB inLen outLen m A' n)
          (T.eval n + 1) (f n z.2) (id z.1)) = f n z.2 := by
    unfold invProb
    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
    congr 1
  have hδ' : ((T.eval n + 1 : ℕ) : ℝ) * ((1 - (D.m.eval n : ℝ) / 2 ^ kkOf (D.m.eval n)) ^ n + 0) ≤
      (T.eval n + 1) * (1 / 2 : ℝ) ^ n := by
    rw [add_zero]
    push_cast
    exact mul_le_mul_of_nonneg_left hδ (by positivity)
  have hkey := (abs_le.1 key).1
  linarith [hL, hR, hkey, hδ']

end TCSlib.Cryptography.OneWay
