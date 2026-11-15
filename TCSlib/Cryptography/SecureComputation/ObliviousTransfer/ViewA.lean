/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Alice's side of Proposition 161.5

Alice's real view of Protocol 160.4 differs from `S_A`'s only in Bob's message: the real pair holds
`y_b = f_i(x) = eval ⟨i, w⟩` for a sampled `w` and a raw sample `y_{1−b}`, the simulated pair two
raw samples. For every generated index `i`, `eval ⟨i, w⟩` is within `2δ(n)` of a raw sample when
the sampler is within `δ(n)` of uniform (`perm_i` is a bijection), so any distinguisher's
advantage is at most `2δ(n)` [PS10, Proposition 161.5, proof].

## Main results

* `OT.statClose_prod_of_forall`: closeness for every value of a shared first coordinate gives
  closeness of the joint samplers.
* `OT.statClose_eval_sample`: `eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)`.
* `OT.realA_realCoins`, `OT.idealA_simACoins`: Alice's real and ideal samplers on typed coins.
* `OT.distAdv_realA_idealA_le`: the bound `2δ(n)` on Alice's side.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5 (book pp. 161–162).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-- **Closeness with a shared first coordinate**: if `X r` is `c`-close to `Y r` for every `r`
(and `0 ≤ c`), then `(r, X r s)` is `c`-close to `(r, Y r t)` over uniform `(r, s)` and `(r, t)`
(`uprob_prod`, `abs_uexp_sub_le`). -/
theorem statClose_prod_of_forall {ρ σ τ γ : Type*} [Fintype ρ] [Fintype σ] [Fintype τ]
    {X : ρ → σ → γ} {Y : ρ → τ → γ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ r, StatClose (X r) (Y r) c) :
    StatClose (fun z : ρ × σ => (z.1, X z.1 z.2)) (fun z : ρ × τ => (z.1, Y z.1 z.2)) c := by
  refine (statClose_iff _ _ _).2 fun P => ?_
  rw [uprob_prod, uprob_prod]
  exact abs_uexp_sub_le hc fun r => (statClose_iff _ _ _).1 (h r) fun g => P (r, g)

/-- **The evaluated sample is close to a raw sample** [PS10, Proposition 161.5, proof]: at every
generated index `i = index n r`, `eval ⟨i, Sample(i; s)⟩` is `2δ(n)`-close to `Sample(i; s)` when
the sampler is within `δ` of uniform.

**Proof sketch.** Decoding the sample is `δ`-close to the uniform element (`SampleClose`). Mapping
by `x ↦ encD (perm x)` gives `eval ⟨i, Sample⟩` (`evalSampled`, `f_perm`) against
`encD (perm x)`, which is `0`-close to `encD x` (`perm` is a bijection, `comp_equiv_left`).
Mapping by `encD` gives `Sample` (canonical decoding) against `encD x`. Chain the three. -/
theorem statClose_eval_sample {δ : ℕ → ℝ} (hδ : T.SampleClose δ) (n : ℕ) (r : T.gen.Coins n) :
    StatClose (fun s : T.sample.Coins n =>
        T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)))
      (fun s => T.sample.runAt n (T.index n r) s) (2 * δ n) := by
  have h₁ := (Collection.sampleClose_iff _ _).1 hδ n r
  have hA : StatClose (fun s : T.sample.Coins n => T.encD (T.index n r) (T.perm (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)))
      (fun x => T.encD (T.index n r) (T.perm (T.index n r) x)) (δ n) :=
    h₁.map fun o => T.encD (T.index n r) (T.perm (T.index n r) (o.getD default))
  have hC : StatClose (fun s : T.sample.Coins n => T.encD (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))
      (fun x => T.encD (T.index n r) x) (δ n) :=
    h₁.map fun o => T.encD (T.index n r) (o.getD default)
  have eA : (fun s : T.sample.Coins n => T.encD (T.index n r) (T.perm (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))) =
      fun s => T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)) := by
    funext s
    obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
    rw [hx, Option.getD_some, hev, T.f_perm]
  have eC : (fun s : T.sample.Coins n => T.encD (T.index n r)
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)) =
      fun s => T.sample.runAt n (T.index n r) s := by
    funext s
    obtain ⟨x, hx, -⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
    rw [hx, Option.getD_some, ((Collection.decD_eq_some_iff _).1 hx).symm]
  rw [eA] at hA
  rw [eC] at hC
  have hB : StatClose (fun x => T.encD (T.index n r) (T.perm (T.index n r) x))
      (fun x => T.encD (T.index n r) x) 0 :=
    (StatClose.refl fun x => T.encD (T.index n r) x).comp_equiv_left (T.perm (T.index n r))
  exact ((hA.trans hB).trans hC.symm).mono (by linarith)

/-- **Alice's real sampler on typed coins**: on `(r, s₁, s₂)` (`realCoins`), it is
`⟨⟨⟨1^n, a⟩, ⟨r, [y, []]⟩⟩, [a_b]⟩` with `y = ⟨eval ⟨i, w₁⟩, w₂⟩` (`⟨w₂, eval ⟨i, w₁⟩⟩` if `b`),
`i = index n r` and `w_j = Sample(i; s_j)`. -/
theorem realA_realCoins {π : Protocol} (hπ : IsOT T H π)
    (hout : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    otFunctionality.realA π n a b ((realCoins T H hπ n).symm p) =
      pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
        (pairEncode (List.ofFn p.1)
          (pairEncode
            (if inB1 b 0 then
              pairEncode (T.sample.runAt n (T.index n p.1) p.2.2)
                (T.eval (pairEncode (T.index n p.1) (T.sample.runAt n (T.index n p.1) p.2.1)))
            else
              pairEncode
                (T.eval (pairEncode (T.index n p.1) (T.sample.runAt n (T.index n p.1) p.2.1)))
                (T.sample.runAt n (T.index n p.1) p.2.2))
            (pairEncode [] []))))
        [inA2 a (if inB1 b 0 then 1 else 0)] := by
  have hlen : (List.ofFn p.2.1).length = T.sample.coins.eval n := length_ofFn_coins _ n _
  rw [Functionality.realA_eq, Protocol.viewP_eq, View.encode_mk, transcriptWith_isOT T H hπ,
    ← ofFn_inA2 a, ← ofFn_inB1 b, hout, ofFn_inA2, ofFn_inB1, realCoins_symm_fst_ofFn,
    realCoins_symm_snd_ofFn, receiverNext_single, List.length_replicate, List.take_left' hlen,
    List.drop_left' hlen, ofFn_eq_inB1, List.headD_cons, ← NUPPT.runAt_eq, ← NUPPT.runAt_eq,
    ← NUPPT.runAt_eq, ← Collection.index_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
    Strategy.encodeMsgs_nil]

/-- **Alice's ideal sampler on typed coins**: on `(r, s₁, s₂)` (`simACoins`), it is
`⟨⟨⟨1^n, a⟩, ⟨r, [⟨w₁, w₂⟩, []]⟩⟩, [a_b]⟩` with `w_j = Sample(index n r; s_j)`. -/
theorem idealA_simACoins {S : NUPPT} (hS : IsSimA T S) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    otFunctionality.idealA S n a b ((simACoins T hS n).symm p) =
      pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
        (pairEncode (List.ofFn p.1)
          (pairEncode (pairEncode (T.sample.runAt n (T.index n p.1) p.2.1)
              (T.sample.runAt n (T.index n p.1) p.2.2))
            (pairEncode [] []))))
        [inA2 a (if inB1 b 0 then 1 else 0)] := by
  rw [Functionality.idealA_eq, ((isSimA_iff T S).1 hS).2, simACoins_symm_ofFn, simAView_layout,
    pairFstD_pairEncode, ofFn_f_snd]

/-- **Alice's side of Proposition 161.5** [PS10]: for a protocol of the shape of Protocol 160.4
(with Bob's output `[a_b]`, `hout`), a machine of `S_A`'s shape and a sampler within `δ` of
uniform, every distinguisher's advantage between Alice's real and ideal samplers is at most
`2δ(n)`: `distAdv (realA π n a b) (idealA S n a b) (D.distinguisherL n) ≤ 2 * δ n`.

**Proof sketch.** Relabel both coin spaces as `Coins_Gen × (Coins_Sample × Coins_Sample)`
(`acceptProb_comp_equiv`). The samplers are then `W r (y_real)` and `W r (y_sim)` for one map
`W` (`realA_realCoins`, `idealA_simACoins`). For each `r`, `y_real` is `2δ(n)`-close to `y_sim`:
`StatClose.prod` of `statClose_eval_sample` with the identical raw sample (after swapping the two
sample blocks when `b`). So the joint samplers are `2δ(n)`-close (`statClose_prod_of_forall`,
`StatClose.map`), and `distAdv_le_of_statClose` concludes. -/
theorem distAdv_realA_idealA_le {π : Protocol} (hπ : IsOT T H π)
    (hout : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
    {S : NUPPT} (hS : IsSimA T S) {δ : ℕ → ℝ} (hδ : T.SampleClose δ) (D : NUPPT) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool) :
    distAdv (otFunctionality.realA π n a b) (otFunctionality.idealA S n a b)
      (D.distinguisherL n) ≤ 2 * δ n := by
  have h0 : 0 ≤ 2 * δ n := by
    have := ((Collection.sampleClose_iff _ _).1 hδ n fun _ => false).nonneg
    linarith
  rw [distAdv_def, ← acceptProb_comp_equiv (realCoins T H hπ n).symm,
    ← acceptProb_comp_equiv (simACoins T hS n).symm, ← distAdv_def]
  simp only [realA_realCoins T H hπ hout, idealA_simACoins T hS]
  refine distAdv_le_of_statClose _ _ ?_ _
  -- the per-index closeness of Bob's message
  have hY : ∀ r : T.gen.Coins n, StatClose
      (fun s : T.sample.Coins n × T.sample.Coins n =>
        if inB1 b 0 then
          pairEncode (T.sample.runAt n (T.index n r) s.2)
            (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s.1)))
        else
          pairEncode (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s.1)))
            (T.sample.runAt n (T.index n r) s.2))
      (fun s : T.sample.Coins n × T.sample.Coins n =>
        pairEncode (T.sample.runAt n (T.index n r) s.1) (T.sample.runAt n (T.index n r) s.2))
      (2 * δ n) := by
    intro r
    have he := statClose_eval_sample T hδ n r
    have hs := StatClose.refl fun s : T.sample.Coins n => T.sample.runAt n (T.index n r) s
    cases hb : inB1 b 0
    · have h := (he.prod hs).map fun q : List Bool × List Bool => pairEncode q.1 q.2
      simpa only [Bool.false_eq_true, if_false, add_zero] using h
    · have h := ((hs.prod he).map fun q : List Bool × List Bool =>
        pairEncode q.1 q.2).comp_equiv_left (Equiv.prodComm (T.sample.Coins n) (T.sample.Coins n))
      simpa only [if_true, zero_add, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] using h
  exact (statClose_prod_of_forall h0 hY).map fun q : T.gen.Coins n × List Bool =>
    pairEncode (pairEncode (pairEncode (List.replicate n true) (List.ofFn a))
      (pairEncode (List.ofFn q.1) (pairEncode q.2 (pairEncode [] []))))
      [inA2 a (if inB1 b 0 then 1 else 0)]

end TCSlib.Cryptography.SecureComputation.OT
