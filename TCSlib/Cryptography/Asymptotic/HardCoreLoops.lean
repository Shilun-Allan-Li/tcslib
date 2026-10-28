/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreLemmas
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# State loops for the hard-core predicate theorems

The loop machines behind the Goldreich–Levin theorem [PS10, Theorem 87.3]: the guarded state
iteration `polyTimeComputable_stateIterate` (an instance of
`Complexity.polyTimeComputable_iterate` on the length-guarded step
`Complexity.StateLoop.gstep`), the block encoding `blocksStr` of a tuple of equal-length bit
strings, the **selective block XOR** `selXorFun` computing `⊕_{t : β_t = 1} s_t` on
`⟨⟨1^m, β⟩, s⟩` — the subset XOR `S_L` of [PS10, Algorithm 89.6] and, with one-bit blocks, the
inner product `⟨x, r⟩` of [PS10, Fact 88.4] (`ipFun`) — and unary halving `1^n ↦ 1^{⌊n/2⌋}`
(`unaryHalf`, for the balanced permutation of `Asymptotic/HardCorePermutation.lean`).

Each loop is specified by the closed form of its orbit on well-formed inputs
(`SelXor.orbit_eq`), its stabilisation (`SelXor.orbit_stable`) and the length bound that
keeps the guard of `gstep` from firing (`SelXor.orbit_length_le`).

## Main definitions

* `TCSlib.Cryptography.blocksEquiv`, `TCSlib.Cryptography.blocksStr` — tuples of blocks as
  one bit string.
* `TCSlib.Cryptography.selXorFun`, `TCSlib.Cryptography.SelXor.partialSum` — the selective
  block XOR and its partial sums.
* `TCSlib.Cryptography.ipFun`, `TCSlib.Cryptography.unaryHalf` — the inner-product evaluator
  and unary halving.

## Main results

* `TCSlib.Cryptography.polyTimeComputable_stateIterate` — guarded state iteration is
  polynomial-time.
* `TCSlib.Cryptography.selXorFun_poly`, `TCSlib.Cryptography.selXorFun_input` — the selective
  block XOR is polynomial-time and computes the subset XOR.
* `TCSlib.Cryptography.ipFun_poly`, `TCSlib.Cryptography.ipFun_ofFn` — the inner-product
  evaluator is polynomial-time and computes `⟨x, r⟩`.
* `TCSlib.Cryptography.unaryHalf_poly` — unary halving is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Fact 88.4, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset Complexity.StateLoop

/-! ## State loops run for a fixed number of rounds -/

/-- **Guarded state iteration.** A state word `⟨x, s⟩` retains the input `x` and evolves its
state from `start x` by the length-guarded step `Complexity.StateLoop.gstep step B`; running it
for `|⟨x, start x⟩|` rounds and reading `out` is polynomial-time (instance of
`Complexity.polyTimeComputable_iterate`, the orbit bound being `StateLoop.length_gstep_iterate_le`).
On inputs whose genuine orbit stays within `B|x|` the guard never fires
(`StateLoop.gstep_iterate_eq`), which is how each loop below is identified with its closed
form. (The pattern of `Complexity.polyTimeComputable_stateFind`, `Randomized/Repetition.lean`,
with a fixed round count instead of an acceptance test.) -/
theorem polyTimeComputable_stateIterate {start step out : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step)
    (hout : PolyTimeComputable out) (B : PolyExpr) :
    PolyTimeComputable fun x =>
      out ((gstep step B)^[(pairEncode x (start x)).length] (pairEncode x (start x))) := by
  have hF := polyTimeComputable_iterate (gstep_poly hstep B) .var (gstepBound B)
    (fun w i _ => length_gstep_iterate_le step B w i)
  have hpre : PolyTimeComputable fun x => pairEncode x (start x) :=
    polyTimeComputable_id.pairEncode hstart
  exact hout.comp (hF.comp hpre)

/-- Bitwise XOR of two polynomial-time maps is polynomial-time
(`Complexity.polyTimeComputable_pairXor` on the pair). -/
theorem zipXor_poly {a b : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) : PolyTimeComputable fun w => List.zipWith xor (a w) (b w) := by
  convert polyTimeComputable_pairXor.comp (ha.pairEncode hb) using 1
  funext w
  simp

/-! ## Blocks of bit strings -/

/-- A string of `q · ℓ` bits as `q` consecutive blocks of `ℓ` bits (private copy of
`FunFamily.blocks`, `Asymptotic/OneWay.lean`). -/
def blocksEquiv (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The inverse of `blocksEquiv` reads block `p.divNat`, position `p.modNat`. -/
theorem blocksEquiv_symm_apply (q ℓ : ℕ) (t : Fin q → Fin ℓ → Bool) (p : Fin (q * ℓ)) :
    (blocksEquiv q ℓ).symm t p = t p.divNat p.modNat := rfl

/-- The encoding of a tuple of `k` blocks of `m` bits as one string of `k · m` bits. -/
def blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) : List Bool :=
  List.ofFn ((blocksEquiv k m).symm s)

/-- The length of the block encoding. -/
@[simp] theorem length_blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) :
    (blocksStr s).length = k * m := List.length_ofFn

/-- Block `i` of the block encoding: the `m` bits after the first `i · m`. 

**Proof sketch.** `List.ext_getElem`: the length is `min m (k·m − i·m) = m`; position `j` of the block is position `i·m + j` of the encoding, whose block index is `i` and offset `j` (`Nat.add_mul_div_right`, `Nat.add_mul_mod_self_right`). -/
theorem take_drop_blocksStr {k m : ℕ} (s : Fin k → Fin m → Bool) (i : Fin k) :
    ((blocksStr s).drop (i * m)).take m = List.ofFn (s i) := by
  have hm : 0 < m ∨ m = 0 := by omega
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_take, List.length_drop, length_blocksStr, List.length_ofFn]
    have := i.isLt
    rcases hm with hm | hm
    · refine min_eq_left ?_
      rw [← Nat.sub_mul]
      exact Nat.le_mul_of_pos_left m (by omega)
    · simp [hm]
  · simp only [List.length_ofFn] at hj₂
    simp only [List.getElem_take, List.getElem_drop, blocksStr, List.getElem_ofFn,
      blocksEquiv_symm_apply]
    have hmpos : 0 < m := by omega
    congr 1
    · refine Fin.ext ?_
      simp only [Fin.coe_divNat]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hmpos, Nat.div_eq_of_lt hj₂, zero_add]
    · refine Fin.ext ?_
      simp only [Fin.coe_modNat]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj₂]

/-- The block encoding of a tuple of one-bit blocks is the string of the bits. -/
theorem blocksStr_one {k : ℕ} (r : Fin k → Bool) :
    blocksStr (fun t (_ : Fin 1) => r t) = List.ofFn r := by
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [blocksStr, List.getElem_ofFn, blocksEquiv_symm_apply]
  congr 1
  exact Fin.ext (by simp [Fin.coe_divNat])

/-- Bitwise XOR of two encoded strings is the encoding of the pointwise sum (`Bool` as a
Boolean ring, `+` is XOR). -/
theorem zipWith_xor_ofFn {m : ℕ} (a b : Fin m → Bool) :
    List.zipWith xor (List.ofFn a) (List.ofFn b) = List.ofFn (a + b) := by
  refine List.ext_getElem (by simp) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_zipWith, List.getElem_ofFn, Pi.add_apply]
  rfl

/-! ## The selective block XOR `⊕_{t : β_t = 1} s_t` -/

namespace SelXor

/-- The partial subset sum `∑_{t < i, β_t = 1} s_t` of the blocks `s_t`, by recursion on `i`. -/
def partialSum {k m : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) : ℕ → (Fin m → Bool)
  | 0 => 0
  | i + 1 => partialSum β s i + if h : i < k then (if β ⟨i, h⟩ then s ⟨i, h⟩ else 0) else 0

/-- The partial sum is the subset sum over the indices `t < i` with `β_t = 1`. 

**Proof sketch.** Induction on `i`; the filter at `i + 1` splits the term `t = i` off the filter at `i` (`Finset.sum_filter`, `Finset.sum_add_distrib`, `Finset.sum_eq_single`). -/
theorem partialSum_eq {k m : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) :
    partialSum β s i = ∑ t ∈ univ.filter (fun t : Fin k => (t : ℕ) < i ∧ β t = true), s t := by
  induction i with
  | zero => simp [partialSum]
  | succ i ih =>
    rw [partialSum, ih, Finset.sum_filter, Finset.sum_filter]
    by_cases hi : i < k
    · rw [dif_pos hi]
      have hsplit : ∀ t : Fin k,
          (if (t : ℕ) < i + 1 ∧ β t = true then s t else 0) =
            (if (t : ℕ) < i ∧ β t = true then s t else 0) +
              (if t = ⟨i, hi⟩ ∧ β t = true then s t else 0) := by
        intro t
        by_cases ht : t = ⟨i, hi⟩
        · subst ht
          simp
        · have ht' : (t : ℕ) ≠ i := fun h => ht (Fin.ext h)
          by_cases hb : β t = true
          · by_cases hlt : (t : ℕ) < i
            · simp [hlt, hb, ht, Nat.lt_succ_of_lt hlt]
            · have : ¬ (t : ℕ) < i + 1 := by omega
              simp [hlt, hb, ht, this]
          · simp [hb]
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single ⟨i, hi⟩ (fun t _ ht => by simp [ht]) (fun h => absurd (mem_univ _) h)]
      simp
    · rw [dif_neg hi, add_zero]
      refine Finset.sum_congr rfl fun t _ => ?_
      have : ((t : ℕ) < i + 1 ↔ (t : ℕ) < i) := by have := t.isLt; omega
      simp [this]


/-- The initial state on the input `⟨⟨1^m, β⟩, s⟩`: `⟨β, ⟨s, 1^m ⊕ 1^m⟩⟩` (the accumulator starts
at `0^m`). -/
def start (x : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD x))
    (pairEncode (pairSndD x) (List.zipWith xor (pairFstD (pairFstD x)) (pairFstD (pairFstD x))))

/-- The step on the state word `⟨⟨⟨1^m, β⟩, s⟩, ⟨β', ⟨s', acc⟩⟩⟩`: if `β'` is empty, stay;
otherwise consume its first bit `b`, drop one block of `m` bits from `s'`, and XOR that block
into `acc` when `b = 1`. -/
def step (w : List Bool) : List Bool :=
  if pairFstD (pairSndD w) = [] then pairSndD w else
    pairEncode (pairFstD (pairSndD w)).tail
      (pairEncode ((pairFstD (pairSndD (pairSndD w))).drop (pairFstD (pairFstD (pairFstD w))).length)
        (if (pairFstD (pairSndD w)).headD false then
          List.zipWith xor (pairSndD (pairSndD (pairSndD w)))
            ((pairFstD (pairSndD (pairSndD w))).take (pairFstD (pairFstD (pairFstD w))).length)
        else pairSndD (pairSndD (pairSndD w))))

/-- The output: the accumulator of the final state word. -/
def out (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))

/-- The length bound on the states of the loop. -/
def bound : PolyExpr := .mul (.const 2) .var

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_pairSndD.pairEncode
      (zipXor_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
        (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- The step is polynomial-time (`polyTimeComputable_ite` on the emptiness test, the FP
toolkit of `Complexity.StateLoop`, `takeLen_poly`/`dropLen_poly` and `zipXor_poly`). 

**Proof sketch.** The branch on `β' = []` is `polyTimeComputable_ite` with `isNil_poly`; the body pairs `tail_poly` with the dropped block (`dropLen_poly`) and the conditional XOR (`polyTimeComputable_ite` on `headBit_poly`, `zipXor_poly` with `takeLen_poly`). -/
theorem step_poly : PolyTimeComputable step := by
  have hβ : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hu : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hs : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hacc : PolyTimeComputable fun w => pairSndD (pairSndD (pairSndD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have htest : PolyTimeComputable fun w => [decide (pairFstD (pairSndD w) = [])] := isNil_poly.comp hβ
  have hhead : PolyTimeComputable fun w => [(pairFstD (pairSndD w)).headD false] :=
    headBit_poly.comp hβ
  have hbody : PolyTimeComputable fun w =>
      pairEncode (pairFstD (pairSndD w)).tail
        (pairEncode ((pairFstD (pairSndD (pairSndD w))).drop (pairFstD (pairFstD (pairFstD w))).length)
          (if (pairFstD (pairSndD w)).headD false then
            List.zipWith xor (pairSndD (pairSndD (pairSndD w)))
              ((pairFstD (pairSndD (pairSndD w))).take (pairFstD (pairFstD (pairFstD w))).length)
          else pairSndD (pairSndD (pairSndD w)))) :=
    (tail_poly.comp hβ).pairEncode ((dropLen_poly hu hs).pairEncode
      (polyTimeComputable_ite hhead (zipXor_poly hacc (takeLen_poly hu hs)) hacc))
  convert polyTimeComputable_ite htest polyTimeComputable_pairSndD hbody using 1
  funext w
  simp only [step, decide_eq_true_eq]

/-- The output is polynomial-time. -/
theorem out_poly : PolyTimeComputable out :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-- The well-formed input `⟨⟨1^m, β⟩, s⟩` for `β ∈ {0,1}^k` and `k` blocks `s_t ∈ {0,1}^m`. -/
def input (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) : List Bool :=
  pairEncode (pairEncode (List.replicate m true) (List.ofFn β)) (blocksStr s)

/-- The closed form of the orbit on a well-formed input, for `i ≤ k` rounds:
`⟨β.drop i, ⟨s.drop (i·m), partialSum β s i⟩⟩`. 

**Proof sketch.** Induction on `i`: the initial accumulator `1^m ⊕ 1^m` is `0^m` (`List.zipWith_replicate`, `List.ofFn_const`); at round `i < k` the head of `β.drop i` is `β_i` (`List.drop_eq_getElem_cons`), the block is `take_drop_blocksStr`, and the accumulator update is `zipWith_xor_ofFn` against the recursion of `partialSum`. -/
theorem orbit_eq (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) (hi : i ≤ k) :
    orbit start step (input m β s) i =
      pairEncode ((List.ofFn β).drop i)
        (pairEncode ((blocksStr s).drop (i * m)) (List.ofFn (partialSum β s i))) := by
  induction i with
  | zero =>
    simp only [orbit_zero, start, input, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_zero,
      Nat.zero_mul, partialSum, List.zipWith_replicate, Nat.min_self]
    congr 2
    rw [Bool.xor_self]
    exact (List.ofFn_const m false).symm
  | succ i ih =>
    have hi' : i < k := hi
    rw [orbit_succ, ih (Nat.le_of_succ_le hi)]
    unfold step
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, input, List.length_replicate]
    have hne : (List.ofFn β).drop i ≠ [] := by
      rw [Ne, List.drop_eq_nil_iff, List.length_ofFn]; omega
    rw [if_neg hne, List.tail_drop, List.drop_drop,
      List.drop_eq_getElem_cons (i := i) (l := List.ofFn β) (by rw [List.length_ofFn]; exact hi'),
      List.headD_cons, List.getElem_ofFn, take_drop_blocksStr s ⟨i, hi'⟩]
    congr 2
    · rw [Nat.succ_mul]
    · rw [partialSum, dif_pos hi']
      by_cases hb : β ⟨i, hi'⟩ = true
      · rw [if_pos hb, if_pos hb, zipWith_xor_ofFn]
      · rw [if_neg hb, if_neg hb, add_zero]

/-- After `k` rounds the loop is stationary (`β'` is exhausted). -/
theorem orbit_stable (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (j : ℕ) :
    orbit start step (input m β s) (k + j) = orbit start step (input m β s) k := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, orbit_succ, ih, orbit_eq m β s k le_rfl]
    unfold step
    simp [List.drop_eq_nil_of_le]

/-- Every state of the loop on a well-formed input has length at most `2|input|`. -/
theorem orbit_length_le (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) (i : ℕ) :
    (orbit start step (input m β s) i).length ≤ bound.eval (input m β s).length := by
  have key : ∀ i ≤ k, (orbit start step (input m β s) i).length ≤ bound.eval (input m β s).length := by
    intro i hi
    rw [orbit_eq m β s i hi]
    simp only [bound, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, input,
      length_pairEncode, List.length_drop, List.length_ofFn, List.length_replicate, length_blocksStr]
    omega
  rcases le_or_gt i k with hi | hi
  · exact key i hi
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    rw [orbit_stable]
    exact key k le_rfl

end SelXor

/-- **The selective block XOR**: on `⟨⟨1^m, β⟩, s⟩` with `β ∈ {0,1}^k` and `s` a string of `k`
blocks of `m` bits, output `⊕_{t : β_t = 1} s_t` (the subset XOR `S_L` of [PS10, Algorithm 89.6]
for `L = {t | β_t = 1}`, and the inner product `⟨x, r⟩` for `m = 1`). Realised as the guarded
state loop `SelXor.step` run for `|⟨x, start x⟩|` rounds. -/
def selXorFun (x : List Bool) : List Bool :=
  SelXor.out ((gstep SelXor.step SelXor.bound)^[(pairEncode x (SelXor.start x)).length]
    (pairEncode x (SelXor.start x)))

/-- The selective block XOR is polynomial-time. -/
theorem selXorFun_poly : PolyTimeComputable selXorFun :=
  polyTimeComputable_stateIterate SelXor.start_poly SelXor.step_poly SelXor.out_poly SelXor.bound

/-- **The selective block XOR computes the subset XOR**: on the well-formed input
`⟨⟨1^m, β⟩, s⟩` it outputs the encoding of `∑_{t : β_t = 1} s_t` (`Bool` as a Boolean ring).

**Proof sketch.** The genuine orbit is bounded (`SelXor.orbit_length_le`), so the guard never
fires (`StateLoop.gstep_iterate_eq`); the loop runs for `R ≥ k` rounds, is stationary after `k`
(`SelXor.orbit_stable`), and its state after `k` rounds is `SelXor.orbit_eq` with
`SelXor.partialSum_eq`. -/
theorem selXorFun_input (m : ℕ) {k : ℕ} (β : Fin k → Bool) (s : Fin k → Fin m → Bool) :
    selXorFun (SelXor.input m β s) =
      List.ofFn (∑ t ∈ univ.filter (fun t : Fin k => β t = true), s t) := by
  unfold selXorFun
  set R := (pairEncode (SelXor.input m β s) (SelXor.start (SelXor.input m β s))).length with hR
  have hRk : k ≤ R := by
    rw [hR, length_pairEncode, SelXor.input, length_pairEncode, length_pairEncode, List.length_ofFn]
    omega
  rw [gstep_iterate_eq SelXor.start SelXor.step SelXor.bound _ R
    (fun i _ => SelXor.orbit_length_le m β s i) R le_rfl]
  obtain ⟨j, hj⟩ : ∃ j, R = k + j := ⟨R - k, by omega⟩
  rw [hj, SelXor.orbit_stable, SelXor.orbit_eq m β s k le_rfl, SelXor.out, pairSndD_pairEncode,
    pairSndD_pairEncode, pairSndD_pairEncode, SelXor.partialSum_eq]
  congr 2
  refine Finset.filter_congr fun t _ => ?_
  simp [t.isLt]

/-! ## The inner product `⟨x, r⟩` and unary halving -/

/-- The inner-product evaluator on `⟨x, r⟩`: the selective block XOR with one-bit blocks. -/
def ipFun (z : List Bool) : List Bool :=
  selXorFun (pairEncode (pairEncode [true] (pairFstD z)) (pairSndD z))

/-- Composition of polynomial-time functions, in applied form (so that the unifier never
unfolds the outer function; private copy of `ptc_comp` in `Randomized/Closure.lean`). -/
theorem ptcComp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The inner-product evaluator is polynomial-time. -/
theorem ipFun_poly : PolyTimeComputable ipFun := by
  have h := ptcComp (g := selXorFun) selXorFun_poly
    (((polyTimeComputable_const [true]).pairEncode polyTimeComputable_pairFstD).pairEncode
      polyTimeComputable_pairSndD)
  exact h

/-- `⟨x, r⟩ = ∑_{t : x_t = 1} r_t` in the Boolean ring `Bool`. -/
theorem ip_eq_sum_filter {k : ℕ} (x r : Fin k → Bool) :
    HardcoreBit.ip x r = ∑ t ∈ univ.filter (fun t : Fin k => x t = true), r t := by
  rw [HardcoreBit.ip, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases x t <;> cases r t <;> rfl

/-- **The inner-product evaluator computes `⟨x, r⟩`** on encoded strings of equal length. -/
theorem ipFun_ofFn {k : ℕ} (x r : Fin k → Bool) :
    ipFun (pairEncode (List.ofFn x) (List.ofFn r)) = [HardcoreBit.ip x r] := by
  unfold ipFun
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  have hin : pairEncode (pairEncode [true] (List.ofFn x)) (List.ofFn r) =
      SelXor.input 1 x (fun t (_ : Fin 1) => r t) := by
    rw [SelXor.input, blocksStr_one]
    rfl
  rw [hin, selXorFun_input, ip_eq_sum_filter, List.ofFn_succ, List.ofFn_zero, Finset.sum_apply]

/-- Unary halving `1^n ↦ 1^{⌊n/2⌋}`. -/
def unaryHalf (u : List Bool) : List Bool := List.replicate (u.length / 2) true

/-- Unary halving is polynomial-time: the block map with blocks of two symbols and the constant
emission `[true]` (`Complexity.polyTimeComputable_blockMap`) emits one `true` per full block. -/
theorem unaryHalf_poly : PolyTimeComputable unaryHalf := by
  convert (polyTimeComputable_blockMap (.const 2) (polyTimeComputable_const [true])).comp
    ((polyTimeComputable_const []).pairEncode polyTimeComputable_id) using 1
  funext u
  simp only [Function.comp_apply, pairSndD_pairEncode, PolyExpr.eval_const, unaryHalf, id]
  rw [← List.map_eq_flatMap, List.map_const', List.length_range]

end TCSlib.Cryptography
