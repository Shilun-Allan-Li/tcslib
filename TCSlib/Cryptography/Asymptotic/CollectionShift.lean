/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Constant shifts of trapdoor collections

Replace the security parameter `n` by `n+c` in all three uniform machines of
a trapdoor permutation collection [PS10, Definition 56.1]. This lets collections with a small-parameter
fallback schedule supply exact polynomial encoding widths.

## Main definitions

* `TrapdoorCollection.shiftParameter` shifts the generator, sampler and inverter together.
* `TrapdoorCollection.shiftGenCoins`, `shiftSampleCoins` and `shiftInvCoins` match their tapes.

## Main results

* `TrapdoorCollection.shiftParameter_encD_length` transports exact encoding widths.
* `TrapdoorCollection.shiftParameter_sampleClose` transports sampler closeness.
* `TrapdoorCollection.shiftParameter_oneWay` transports one-wayness.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
-/

namespace TCSlib.Cryptography.TrapdoorCollection

open Complexity Turing

/-- A uniformity-preserving parameter change and its coin and activation laws. -/
private structure ShiftedMachine (A : NUPPT) (c : ℕ) where
  machine : NUPPT
  uniform : A.Uniform → machine.Uniform
  coins : ∀ n, machine.Coins n ≃ A.Coins (n + c)
  coins_ofFn : ∀ n (r : machine.Coins n), List.ofFn (coins n r) = List.ofFn r
  runAt_eq : ∀ n y (r : machine.Coins n), machine.runAt n y r = A.runAt (n + c) y (coins n r)

/-- The polynomial parameter-change machine has the required tape and activation laws.

**Proof sketch.** Instantiate the existing machine with the additive polynomial.
Transport the tapes using the coin-length equality and preserve their raw encodings. -/
private theorem shiftedMachine_exists (A : NUPPT) (c : ℕ) : Nonempty (ShiftedMachine A c) := by
  obtain ⟨B, hBc, hBu, hBr⟩ := A.exists_reparam (.add .var (.const c))
  have hlen (n : ℕ) : B.coinLen n = A.coinLen (n + c) := by
    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst, PolyExpr.eval_add, PolyExpr.eval_var,
      PolyExpr.eval_const]
  let e (n : ℕ) : B.Coins n ≃ A.Coins (n + c) :=
    Equiv.arrowCongr (finCongr (hlen n)) (Equiv.refl Bool)
  have he (n : ℕ) (r : B.Coins n) : List.ofFn (e n r) = List.ofFn r :=
    (List.ofFn_congr (hlen n) r).symm
  refine ⟨⟨B, hBu, e, he, fun n y r => ?_⟩⟩
  simp only [NUPPT.runAt_eq, he, hBr, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]

/-- Choose the certified machine for this constant shift. -/
private noncomputable def shiftedMachine (A : NUPPT) (c : ℕ) : ShiftedMachine A c :=
  Classical.choice (shiftedMachine_exists A c)

/-- Shift the security parameter of the generator, sampler, and inverter from n to n+c.
Keep the domains, encoded permutation, evaluator, and decoder of [PS10, Definition 56.1].

**Proof sketch.** Apply the same polynomial parameter change to the three machines.
Use their activation laws to transfer sampler membership and trapdoor inversion on
each generator tape. -/
noncomputable def shiftParameter (T : TrapdoorCollection) (c : ℕ) : TrapdoorCollection :=
  { T with
    gen := (shiftedMachine T.gen c).machine
    gen_uniform := (shiftedMachine T.gen c).uniform T.gen_uniform
    sample := (shiftedMachine T.sample c).machine
    sample_uniform := (shiftedMachine T.sample c).uniform T.sample_uniform
    sample_spec := by
      intro n r s
      rw [(shiftedMachine T.gen c).runAt_eq, (shiftedMachine T.sample c).runAt_eq]
      exact T.sample_spec (n + c) ((shiftedMachine T.gen c).coins n r)
        ((shiftedMachine T.sample c).coins n s)
    inv := (shiftedMachine T.inv c).machine
    inv_uniform := (shiftedMachine T.inv c).uniform T.inv_uniform
    inv_spec := by
      intro n r
      rw [(shiftedMachine T.gen c).runAt_eq]
      intro y s
      rw [(shiftedMachine T.inv c).runAt_eq]
      exact T.inv_spec (n + c) ((shiftedMachine T.gen c).coins n r) y
        ((shiftedMachine T.inv c).coins n s) }

/-- The shifted and original generator tapes have the same length at corresponding parameters. -/
noncomputable def shiftGenCoins (T : TrapdoorCollection) (c n : ℕ) :
    (T.shiftParameter c).gen.Coins n ≃ T.gen.Coins (n + c) :=
  (shiftedMachine T.gen c).coins n

/-- The generator coin transport preserves the encoded tape. -/
theorem shiftGenCoins_ofFn (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
    List.ofFn (T.shiftGenCoins c n r) = List.ofFn r :=
  (shiftedMachine T.gen c).coins_ofFn n r

/-- The shifted and original sampler tapes have the same length at corresponding parameters. -/
noncomputable def shiftSampleCoins (T : TrapdoorCollection) (c n : ℕ) :
    (T.shiftParameter c).sample.Coins n ≃ T.sample.Coins (n + c) :=
  (shiftedMachine T.sample c).coins n

/-- The sampler coin transport preserves the encoded tape. -/
theorem shiftSampleCoins_ofFn (T : TrapdoorCollection) (c n : ℕ)
    (r : (T.shiftParameter c).sample.Coins n) :
    List.ofFn (T.shiftSampleCoins c n r) = List.ofFn r :=
  (shiftedMachine T.sample c).coins_ofFn n r

/-- The shifted and original inverter tapes have the same length at corresponding parameters. -/
noncomputable def shiftInvCoins (T : TrapdoorCollection) (c n : ℕ) :
    (T.shiftParameter c).inv.Coins n ≃ T.inv.Coins (n + c) :=
  (shiftedMachine T.inv c).coins n

/-- The inverter coin transport preserves the encoded tape. -/
theorem shiftInvCoins_ofFn (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).inv.Coins n) :
    List.ofFn (T.shiftInvCoins c n r) = List.ofFn r :=
  (shiftedMachine T.inv c).coins_ofFn n r

/-- The shifted generator at n returns the original output at n+c. -/
theorem shiftParameter_gen_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
    (r : (T.shiftParameter c).gen.Coins n) :
    (T.shiftParameter c).gen.runAt n y r = T.gen.runAt (n + c) y (T.shiftGenCoins c n r) :=
  (shiftedMachine T.gen c).runAt_eq n y r

/-- The shifted sampler at n returns the original output at n+c. -/
theorem shiftParameter_sample_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
    (r : (T.shiftParameter c).sample.Coins n) :
    (T.shiftParameter c).sample.runAt n y r = T.sample.runAt (n + c) y (T.shiftSampleCoins c n r) :=
  (shiftedMachine T.sample c).runAt_eq n y r

/-- The shifted inverter at n returns the original output at n+c. -/
theorem shiftParameter_inv_runAt (T : TrapdoorCollection) (c n : ℕ) (y : List Bool)
    (r : (T.shiftParameter c).inv.Coins n) :
    (T.shiftParameter c).inv.runAt n y r = T.inv.runAt (n + c) y (T.shiftInvCoins c n r) :=
  (shiftedMachine T.inv c).runAt_eq n y r

/-- The shifted generator returns the same index at n as the original at n+c. -/
theorem shiftParameter_index (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
    (T.shiftParameter c).index n r = T.index (n + c) (T.shiftGenCoins c n r) := by
  rw [Collection.index_eq, Collection.index_eq, T.shiftParameter_gen_runAt]

/-- The shifted generator returns the same trapdoor at n as the original at n+c. -/
theorem shiftParameter_trap (T : TrapdoorCollection) (c n : ℕ) (r : (T.shiftParameter c).gen.Coins n) :
    (T.shiftParameter c).trap n r = T.trap (n + c) (T.shiftGenCoins c n r) := by
  rw [Collection.trap_eq, Collection.trap_eq, T.shiftParameter_gen_runAt]

/-- The domains of the shifted collection agree with the original domains at every index. -/
def shiftParameter_domEquiv (T : TrapdoorCollection) (c : ℕ) (i : List Bool) :
    (T.shiftParameter c).D i ≃ T.D i := Equiv.refl _

/-- The domain equivalence acts as the identity. -/
theorem shiftParameter_domEquiv_apply (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) : T.shiftParameter_domEquiv c i x = x := rfl

/-- The shifted encoder reads through the original domain. -/
theorem shiftParameter_encD (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) :
    (T.shiftParameter c).encD i x = T.encD i (T.shiftParameter_domEquiv c i x) := rfl

/-- The shifted decoder is the original decoder carried back through the domain equivalence. -/
theorem shiftParameter_decD (T : TrapdoorCollection) (c : ℕ) (i w : List Bool) :
    (T.shiftParameter c).decD i w = (T.decD i w).map (T.shiftParameter_domEquiv c i).symm := by
  show T.decD i w = _
  cases T.decD i w <;> rfl

/-- The shifted permutation reads through the original domain. -/
theorem shiftParameter_perm (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) :
    (T.shiftParameter c).perm i x =
      (T.shiftParameter_domEquiv c i).symm (T.perm i (T.shiftParameter_domEquiv c i x)) := rfl

/-- The shifted evaluator equals the original evaluator. -/
theorem shiftParameter_eval (T : TrapdoorCollection) (c : ℕ) :
    (T.shiftParameter c).eval = T.eval := rfl

/-- The shifted function reads through the original domain. -/
theorem shiftParameter_f (T : TrapdoorCollection) (c : ℕ) (i : List Bool)
    (x : (T.shiftParameter c).D i) :
    (T.shiftParameter c).f i x = T.f i (T.shiftParameter_domEquiv c i x) := rfl

/-- Exact encoding widths transfer to the shifted parameter for every generator tape.

**Proof sketch.** Generalize over the domain element and rewrite the generated index
using the generator coin equivalence. The shifted encoding is the original one. -/
theorem shiftParameter_encD_length (T : TrapdoorCollection) (c : ℕ) (W : ℕ → ℕ)
    (h : ∀ n (r : T.gen.Coins n) (x : T.D (T.index n r)), (T.encD (T.index n r) x).length = W n)
    (n : ℕ) (r : (T.shiftParameter c).gen.Coins n)
    (x : (T.shiftParameter c).D ((T.shiftParameter c).index n r)) :
    ((T.shiftParameter c).encD ((T.shiftParameter c).index n r) x).length = W (n + c) := by
  revert x
  change ∀ x : T.D ((T.shiftParameter c).index n r), (T.encD _ x).length = W (n + c)
  rw [T.shiftParameter_index]
  exact h (n + c) (T.shiftGenCoins c n r)

/-- Statistical closeness at n+c transfers to the shifted sampler at n.

**Proof sketch.** Match each generator tape with its original tape. Relabel the uniform
sampler tape along the coin equivalence, using the sampler's activation law. -/
theorem shiftParameter_sampleClose (T : TrapdoorCollection) (c : ℕ) (δ : ℕ → ℝ)
    (h : T.toCollection.SampleClose δ) :
    (T.shiftParameter c).toCollection.SampleClose (fun n => δ (n + c)) := by
  rw [Collection.sampleClose_iff] at h ⊢
  intro n r
  change StatClose
    (fun s : (T.shiftParameter c).sample.Coins n =>
      T.decD ((T.shiftParameter c).index n r)
        ((T.shiftParameter c).sample.runAt n ((T.shiftParameter c).index n r) s))
    (fun x : T.D ((T.shiftParameter c).index n r) => some x) (δ (n + c))
  rw [T.shiftParameter_index]
  simp only [T.shiftParameter_sample_runAt]
  exact (h (n + c) (T.shiftGenCoins c n r)).comp_equiv_left (T.shiftSampleCoins c n)

/-- Each adversary for the shifted collection has an original-parameter adversary with
the same inversion probability at m=n+c.

**Proof sketch.** Run A at m-c with the first A.coinLen(m-c) bits. Relabel the
generator tape and split the longer adversary tape into the consumed prefix and an
independent suffix. Averaging over the unread suffix leaves the event probability
unchanged. -/
theorem shiftParameter_exists_invProbAt (T : TrapdoorCollection) (c : ℕ) (A : NUPPT) :
    ∃ B : NUPPT, ∀ n,
      (T.shiftParameter c).toCollection.invProbAt A n = T.toCollection.invProbAt B (n + c) := by
  obtain ⟨B, hBc, hB⟩ := A.exists_reparam_advice (fun m => m - c) .var
    (fun m => by rw [PolyExpr.eval_var]; exact Nat.sub_le m c)
  refine ⟨B, fun n => ?_⟩
  have hlen : B.coinLen (n + c) =
      A.coinLen n + (A.coinLen (n + c) - A.coinLen n) := by
    have hle : A.coinLen n ≤ A.coinLen (n + c) := by
      simp only [NUPPT.coinLen_eq]
      exact A.coins.eval_mono (Nat.le_add_right n c)
    simp only [NUPPT.coinLen_eq, hBc, PolyExpr.eval_subst, PolyExpr.eval_var] at hle ⊢
    omega
  let e := EnsembleLemmas.coinsEquiv hlen
  simp only [Collection.invProbAt_eq]
  rw [← HardcoreBit.uexp_comp_equiv (T.shiftGenCoins c n)]
  congr 1
  funext r
  let i := (T.shiftParameter c).index n r
  change uprob (fun z : T.D i × A.Coins n =>
    ∃ x', T.decD i (A.runAt n (pairEncode i (T.f i z.1)) z.2) = some x' ∧
      T.f i x' = T.f i z.1) = _
  have hi : i = T.index (n + c) (T.shiftGenCoins c n r) := T.shiftParameter_index c n r
  rw [hi]
  rw [uprob_prod, uprob_prod]
  congr 1
  funext x
  rw [← uprob_comp_equiv e]
  simp only [NUPPT.runAt_eq, hB, Nat.add_sub_cancel, e, EnsembleLemmas.take_ofFn_coinsEquiv]
  exact (uprob_fst _).symm

/-- Constant right shifts preserve one-wayness for trapdoor permutation collections
[PS10, Definitions 41.1 and 56.1; parameter-change consequence].

**Proof sketch.** Shift the sampler error by the same offset. Apply the inversion
probability equality to each adversary, then use negligibility along n ↦ n+c in both
cases. -/
theorem shiftParameter_oneWay (T : TrapdoorCollection) (c : ℕ) (h : T.OneWay) :
    (T.shiftParameter c).OneWay := by
  rw [TrapdoorCollection.oneWay_iff] at h ⊢
  obtain ⟨δ, hδ, hclose⟩ := h.sampleClose
  refine ⟨⟨_, hδ.comp_of_le (fun n => n + c) (fun n => Nat.le_add_right n c),
    T.shiftParameter_sampleClose c δ hclose⟩, fun A => ?_⟩
  obtain ⟨B, hB⟩ := T.shiftParameter_exists_invProbAt c A
  have hshift := (h.hard B).comp_of_le (fun n => n + c) (fun n => Nat.le_add_right n c)
  exact (funext hB) ▸ hshift

end TCSlib.Cryptography.TrapdoorCollection
