/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandom generators and stretch extension

The concrete layer of [Gar26, §3.3 and §3.3.1]. A pseudorandom generator is a map `G`
from seeds to longer strings whose output on a uniform seed is computationally
indistinguishable from uniform; at one fixed value of the security parameter this is
measured by the advantage `prgAdv G D` of a distinguisher `D`.

The main result is the stretch extension of [Gar26, Theorem 3.1]: a generator `G` with
one bit of stretch, iterated `l` times, yields a generator `prgExt G l` with `l` bits of
stretch, and any distinguisher for `prgExt G l` with advantage `ε` turns into an explicit
distinguisher for `G` with advantage at least `ε / l`, via the source's hybrids.

The general statements use structured types: a one-bit-stretch generator is a map
`G : S → Bool × S` (the output bit and the next seed) on an arbitrary finite seed type `S`,
and the extension outputs `(Fin l → Bool) × S`. The bit-string statements are
`prgExtBits` and `exists_prgExtBitsRed_ge`, obtained by composing with the canonical
encodings `Fin (n + 1) → Bool ≃ Bool × (Fin n → Bool)` and
`(Fin l → Bool) × (Fin n → Bool) ≃ (Fin (l + n) → Bool)`.

## Main definitions

* `prgAdv G D`: the distinguishing advantage between `G` on a uniform seed and a uniform
  string [Gar26, Definition 3.5].
* `prgExt G l`: the iterated generator of [Gar26, Construction 3.1].
* `prgHybrid G l k`: the hybrid `H_k` of [Gar26, proof of Theorem 3.1].
* `prgExtRed G l k D`: the reduction at hybrid index `k`.
* `prgExtAvgRed G l D`: the reduction with a uniformly random hybrid index.
* `prgExtBits`, `prgExtBitsRed`: the bit-string versions.

## Main results

* `prgExt_succ`: the closed form of `prgExt` satisfies the recursion of the construction.
* `exists_prgExtRed_ge`: [Gar26, Theorem 3.1], some `k` has advantage `≥ ε / l`.
* `prgAdv_prgExtAvgRed`: the averaged reduction has advantage exactly `ε / l`.
* `exists_prgExtBitsRed_ge`: [Gar26, Theorem 3.1] on bit strings.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3 (Definition 3.5) and §3.3.1 (Construction 3.1,
  Theorem 3.1).
-/

namespace TCSlib.Cryptography

open Finset

variable {S σ ρ γ δ : Type*} [Fintype S] [Fintype σ] [Fintype ρ]

/-! ### Pseudorandom generators -/

/-- The PRG advantage of a distinguisher `D` against `G : σ → γ`: the distinguishing
advantage `|Pr[D(G(s)) = 1] - Pr[D(u) = 1]|` between the output of `G` on a uniform seed
`s` and a uniform element `u` of the output type. [Gar26, Definition 3.5], the condition
`U_{n+m} ≈ G(U_n)` at one value of the security parameter; `G` is a pseudorandom generator
when this advantage is negligible for every efficient `D`, which is stated in the
asymptotic layer. -/
noncomputable def prgAdv [Fintype γ] (G : σ → γ) (D : γ → ρ → Bool) : ℝ :=
  distAdv G (id : γ → γ) D

/-- Re-encoding the output of a generator by a bijection `e` does not change PRG
advantages: the advantage of `D` against `e ∘ G` is that of `D ∘ e` against `G`. -/
theorem prgAdv_comp_equiv [Fintype γ] [Fintype δ] (e : γ ≃ δ) (G : σ → γ)
    (D : δ → ρ → Bool) :
    prgAdv (fun s => e (G s)) D = prgAdv G (fun z r => D (e z) r) := by
  unfold prgAdv distAdv
  rw [← acceptProb_comp_equiv e (id : δ → δ) D]
  rfl

/-! ### Stretch extension -/

/-- The seed update of a one-bit-stretch generator `G : S → Bool × S`: the next seed
`S_i` in `(σ_i, S_i) := G(S_{i-1})`. -/
def prgStep (G : S → Bool × S) : S → S :=
  fun s => (G s).2

/-- The stretch extension of a one-bit-stretch generator [Gar26, Construction 3.1]: from
the seed `S_0`, set `(σ_i, S_i) := G(S_{i-1})` for `i = 1, …, l` and output
`σ_1 σ_2 ⋯ σ_l S_l`. In closed form, with `S_i` the `i`-th iterate of the seed update,
the output bit at (0-indexed) position `i` is the bit of `G(S_i)` and the final seed is
`S_l`; `prgExt_succ` is the recursion of the construction. -/
def prgExt (G : S → Bool × S) (l : ℕ) : S → (Fin l → Bool) × S :=
  fun s => (fun i => (G ((prgStep G)^[i] s)).1, (prgStep G)^[l] s)

omit [Fintype S] in
/-- The stretch extension unrolls one step: `prgExt G (l + 1)` outputs the bit of `G s`
followed by `prgExt G l` on the next seed. [Gar26, Construction 3.1]. -/
theorem prgExt_succ (G : S → Bool × S) (l : ℕ) (s : S) :
    prgExt G (l + 1) s =
      (Fin.cons (G s).1 (prgExt G l (G s).2).1, (prgExt G l (G s).2).2) := by
  refine Prod.ext ?_ ?_
  · funext i
    cases i using Fin.cases with
    | zero => simp [prgExt]
    | succ i => simp [prgExt, Function.iterate_succ_apply, prgStep]
  · simp [prgExt, Function.iterate_succ_apply, prgStep]

/-- The hybrid `H_k` of [Gar26, proof of Theorem 3.1]: the first `k` output bits are
uniform (the first component of the seed), and the remaining `l - k` bits and the final
seed are produced by iterating `G` from a uniform seed `S_k` (the second component).
Seeds are `(Fin l → Bool) × S` for every `k`, the bits beyond the first `k` being ignored,
so that all hybrids share one seed space. -/
def prgHybrid (G : S → Bool × S) (l k : ℕ) : (Fin l → Bool) × S → (Fin l → Bool) × S :=
  fun v => (fun i => if (i : ℕ) < k then v.1 i else (G ((prgStep G)^[i - k] v.2)).1,
    (prgStep G)^[l - k] v.2)

/-- The stretch-extension reduction at hybrid index `k` [Gar26, proof of Theorem 3.1]: on
input `T = (σ, S) ∈ Bool × S`, it draws `k` uniform bits `σ_1, …, σ_k`, takes
`(σ_{k+1}, S_{k+1}) := T`, iterates `G` for the remaining `l - k - 1` steps and calls `D`
once on `σ_1 ⋯ σ_l S_l`. It makes `l - k - 1` calls to `G` and one call to `D`, and draws
`l` uniform bits of which it uses `k`. -/
def prgExtRed (G : S → Bool × S) (l k : ℕ) (D : (Fin l → Bool) × S → ρ → Bool) :
    Bool × S → (Fin l → Bool) × ρ → Bool :=
  fun T c => D (fun i => if (i : ℕ) < k then c.1 i else if (i : ℕ) = k then T.1
    else (G ((prgStep G)^[i - k - 1] T.2)).1, (prgStep G)^[l - k - 1] T.2) c.2

/-- The zeroth hybrid is the stretch extension on a uniform seed: `H_0 ≡ F`. -/
theorem acceptProb_prgHybrid_zero (G : S → Bool × S) (l : ℕ)
    (D : (Fin l → Bool) × S → ρ → Bool) :
    acceptProb (prgHybrid G l 0) D = acceptProb (prgExt G l) D := by
  have h : prgHybrid G l 0 = fun v => prgExt G l v.2 := by
    funext v
    simp [prgHybrid, prgExt]
  rw [h, acceptProb_snd]

/-- The `l`-th hybrid is uniform: `H_l ≡ U_{n+l}`. -/
theorem acceptProb_prgHybrid_self (G : S → Bool × S) (l : ℕ)
    (D : (Fin l → Bool) × S → ρ → Bool) :
    acceptProb (prgHybrid G l l) D = acceptProb (id : (Fin l → Bool) × S → _) D := by
  have h : prgHybrid G l l = id := by
    funext v
    simp [prgHybrid]
  rw [h]

/-- On an output of `G`, the hybrid-`k` reduction simulates the hybrid `H_k`.

**Proof sketch.** With `T = G(S_k)`, the bit at position `k` is the bit of `G(S_k)` and
later bits and the final seed come from iterating `G` from the seed of `G(S_k)`, which
is one more iteration from `S_k`. -/
theorem acceptProb_prgExtRed_left (G : S → Bool × S) {l k : ℕ} (hk : k < l)
    (D : (Fin l → Bool) × S → ρ → Bool) :
    acceptProb G (prgExtRed G l k D) = acceptProb (prgHybrid G l k) D := by
  refine (acceptProb_bind G (fun (T : Bool × S) (u : Fin l → Bool) =>
    ((fun i : Fin l => if (i : ℕ) < k then u i else if (i : ℕ) = k then T.1
      else (G ((prgStep G)^[i - k - 1] T.2)).1), (prgStep G)^[l - k - 1] T.2)) D).trans ?_
  refine Eq.trans ?_ (acceptProb_comp_equiv (Equiv.prodComm _ _) (prgHybrid G l k) D)
  congr 1
  funext w
  have hstep : ∀ m, (prgStep G)^[m] (G w.1).2 = (prgStep G)^[m + 1] w.1 := fun m => by
    rw [Function.iterate_succ_apply]; rfl
  refine Prod.ext ?_ ?_
  · funext i
    simp only [prgHybrid, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rcases lt_trichotomy (i : ℕ) k with h | h | h
    · simp [h]
    · simp [h]
    · simp only [not_lt.mpr h.le, h.ne', if_false, hstep]
      congr 3
      omega
  · simp only [prgHybrid, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, hstep]
    congr 1
    omega

/-- On a uniform input, the hybrid-`k` reduction simulates the hybrid `H_{k+1}`.

**Proof sketch.** The uniform input bit plays the role of the uniform bit at position
`k`; overwriting the unused uniform bit at position `k` with it keeps the bits uniform,
and the uniform input seed is `S_{k+1}`. -/
theorem acceptProb_prgExtRed_right (G : S → Bool × S) {l k : ℕ} (hk : k < l)
    (D : (Fin l → Bool) × S → ρ → Bool) :
    acceptProb (id : Bool × S → _) (prgExtRed G l k D) =
      acceptProb (prgHybrid G l (k + 1)) D := by
  let e : (Bool × S) × (Fin l → Bool) ≃ Bool × ((Fin l → Bool) × S) :=
    { toFun := fun w => (w.1.1, (w.2, w.1.2)), invFun := fun v => ((v.1, v.2.2), v.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  refine (acceptProb_bind (id : Bool × S → _) (fun (T : Bool × S) (u : Fin l → Bool) =>
    ((fun i : Fin l => if (i : ℕ) < k then u i else if (i : ℕ) = k then T.1
      else (G ((prgStep G)^[i - k - 1] T.2)).1), (prgStep G)^[l - k - 1] T.2)) D).trans ?_
  refine Eq.trans ?_ ((acceptProb_comp_equiv e _ D).trans
    (acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin l)
      (fun u (s : S) => prgHybrid G l (k + 1) (u, s)) D))
  congr 1
  funext w
  refine Prod.ext ?_ ?_
  · funext i
    simp only [e, prgHybrid, Function.update_apply, Fin.ext_iff, Equiv.coe_fn_mk, id]
    rcases lt_trichotomy (i : ℕ) k with h | h | h
    · simp [h, Nat.lt_succ_of_lt h, h.ne]
    · simp [h]
    · simp only [not_lt.mpr h.le, h.ne', if_false, not_lt.mpr (Nat.succ_le_of_lt h)]
      congr 3
  · simp only [e, prgHybrid, Equiv.coe_fn_mk, id]
    congr 1

/-- Stretch extension, concrete form [Gar26, Theorem 3.1]: if `D` distinguishes the
`l`-fold extension `prgExt G l` (with `l ≥ 1`) from uniform with advantage `ε`, then for
some hybrid index `k < l` the reduction `prgExtRed G l k D` distinguishes `G` from uniform
with advantage at least `ε / l`.

Deviation: [Gar26] writes the reduction's advantage as the signed difference
`Pr[B(G(U_n)) = 1] - Pr[B(U_{n+1}) = 1]` and then equates it with `|ε_k - ε_{k+1}|`;
the formal statement uses absolute values throughout.

**Proof sketch.** The reduction at `k` accepts outputs of `G` and uniform strings with
the acceptance probabilities of `H_k` and `H_{k+1}`; `H_0` is the extension and `H_l` is
uniform, and some neighbouring pair of hybrids is `ε / l` apart. -/
theorem exists_prgExtRed_ge (G : S → Bool × S) {l : ℕ} (hl : 0 < l)
    (D : (Fin l → Bool) × S → ρ → Bool) :
    ∃ k < l, prgAdv (prgExt G l) D / l ≤ prgAdv G (prgExtRed G l k D) := by
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun i => acceptProb (prgHybrid G l i) D) hl
  refine ⟨k, hk, ?_⟩
  unfold prgAdv distAdv
  rw [acceptProb_prgExtRed_left G hk, acceptProb_prgExtRed_right G hk,
    ← acceptProb_prgHybrid_zero G, ← acceptProb_prgHybrid_self G]
  exact hgap

/-- The uniform stretch-extension reduction: draw the hybrid index `k < l` uniformly at
random and run `prgExtRed G l k D`. It calls `D` once and `G` at most `l - 1` times. -/
def prgExtAvgRed (G : S → Bool × S) (l : ℕ) (D : (Fin l → Bool) × S → ρ → Bool) :
    Bool × S → Fin l × ((Fin l → Bool) × ρ) → Bool :=
  mixDist fun k : Fin l => prgExtRed G l k D

/-- Stretch extension with a uniform reduction: the reduction with a random hybrid index
has advantage against `G` exactly `ε / l`, where `ε` is the advantage of `D` against
`prgExt G l`. [Gar26, Theorem 3.1].

**Proof sketch.** Average the identities of `acceptProb_prgExtRed_left` and
`acceptProb_prgExtRed_right` over `k`; the differences telescope. -/
theorem prgAdv_prgExtAvgRed (G : S → Bool × S) (l : ℕ)
    (D : (Fin l → Bool) × S → ρ → Bool) :
    prgAdv G (prgExtAvgRed G l D) = prgAdv (prgExt G l) D / l := by
  rw [prgAdv, prgExtAvgRed, distAdv_mixDist_eq G _ _ (fun i => acceptProb (prgHybrid G l i) D)
    (fun k => acceptProb_prgExtRed_left G k.isLt D)
    (fun k => acceptProb_prgExtRed_right G k.isLt D), prgAdv, distAdv,
    acceptProb_prgHybrid_zero, acceptProb_prgHybrid_self]

/-! ### Bit strings -/

/-- The stretch extension on bit strings [Gar26, Construction 3.1]: for
`G : {0,1}^n → {0,1}^{n+1}`, read `G(s)` as its first bit and the remaining `n` bits,
iterate `l` times and output the `l` bits followed by the final seed, a string of length
`l + n`. -/
def prgExtBits {n : ℕ} (G : (Fin n → Bool) → Fin (n + 1) → Bool) (l : ℕ) :
    (Fin n → Bool) → Fin (l + n) → Bool :=
  fun s => Fin.appendEquiv l n
    (prgExt (fun s => (Fin.consEquiv fun _ => Bool).symm (G s)) l s)

/-- The bit-string stretch-extension reduction at hybrid index `k`: split the input
`T ∈ {0,1}^{n+1}` into its first bit and the rest, and run `prgExtRed` against the
distinguisher that reads the pair `(σ_1 ⋯ σ_l, S_l)` as the string `σ_1 ⋯ σ_l S_l`. Its
cost is that of `prgExtRed`. -/
def prgExtBitsRed {n : ℕ} (G : (Fin n → Bool) → Fin (n + 1) → Bool) (l k : ℕ)
    (D : (Fin (l + n) → Bool) → ρ → Bool) : (Fin (n + 1) → Bool) → (Fin l → Bool) × ρ → Bool :=
  fun T c => prgExtRed (fun s => (Fin.consEquiv fun _ => Bool).symm (G s)) l k
    (fun z r => D (Fin.appendEquiv l n z) r) ((Fin.consEquiv fun _ => Bool).symm T) c

/-- Stretch extension on bit strings [Gar26, Theorem 3.1]: if `D` distinguishes
`prgExtBits G l` (with `l ≥ 1`) from uniform `l + n`-bit strings with advantage `ε`, then
for some `k < l` the reduction `prgExtBitsRed G l k D` distinguishes `G` from uniform
`n + 1`-bit strings with advantage at least `ε / l`. The output length is written
`l + n` (bits before seed) where the source writes `n + l`. -/
theorem exists_prgExtBitsRed_ge {n : ℕ} (G : (Fin n → Bool) → Fin (n + 1) → Bool)
    {l : ℕ} (hl : 0 < l) (D : (Fin (l + n) → Bool) → ρ → Bool) :
    ∃ k < l, prgAdv (prgExtBits G l) D / l ≤ prgAdv G (prgExtBitsRed G l k D) := by
  obtain ⟨k, hk, h⟩ := exists_prgExtRed_ge (fun s => (Fin.consEquiv fun _ => Bool).symm (G s))
    hl (fun z r => D (Fin.appendEquiv l n z) r)
  refine ⟨k, hk, ?_⟩
  unfold prgExtBits
  rw [prgAdv_comp_equiv]
  rw [prgAdv_comp_equiv] at h
  exact h

end TCSlib.Cryptography
