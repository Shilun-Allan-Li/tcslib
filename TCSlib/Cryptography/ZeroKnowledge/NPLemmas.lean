/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Transfer infrastructure for zero-knowledge proofs along Levin reductions

Proof infrastructure for `TCSlib.Cryptography.ZeroKnowledge.NP` (Claim-124.d, the transfer of
interactive proofs with efficient prover and of zero-knowledge along a Levin reduction
`(f, w)` with length polynomial `p`), kept in a sibling file so that the public statements of
`NP.lean` stay where the audit froze them. Nothing here is specific to 3-colouring.

Three kinds of tools:

* **Executions.** `exec_congr`: two executions whose next-message functions agree on every
  history (possibly with different common inputs, auxiliary inputs and random tapes) have the
  same transcripts.
* **Uniform coin projections.** The pulled-back protocol runs at parameter `|x|` with the coin
  polynomials of `π` evaluated at `p(|x|) = |f x|`, while the machines of the zero-knowledge
  reduction (the verifier `V*'` for `π`, the distinguisher `D'`) run at parameter `|f x| ≥ |x|`
  and read only the first `coinLen |x|` bits of their tapes. A map `g : Ω → Ω'` between finite
  coin spaces is a *uniform projection* (`UnifProj g`) when it is the first component of a
  bijection `Ω ≃ Ω' × K`; the truncation `coinTrunc : (Fin M → Bool) → (Fin m → Bool)` of a coin
  string to its first `m ≤ M` bits is one, uniform projections are closed under products, and
  the law of an event is invariant under them (`UnifProj.uprob_comp`,
  `acceptProb_eq_of_unifProj`, `distAdv_eq_of_unifProj`: "the padding is uniform and
  independent").
* **The machines of the reduction.** `liftVerifier V'` is the verifier `V*'` for `π` obtained
  from a verifier `V'` of the pulled-back protocol (it recovers `x` and `z` from its auxiliary
  input `⟨x, z⟩`, ignores the common input `f x`, and runs `V'` on the first `V'.coinLen |x|`
  coins; `liftVerifier_efficient`); `postView c` re-encodes a view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩`
  of `V*'` as the view `⟨⟨x, z⟩, ⟨r'.take (c |x|), msgs⟩⟩` of `V'` (`postView_encode`,
  `polyTimeComputable_postView`); `exists_liftSimulator` builds the simulator for `V'` from
  the one for `V*'` (`NUPPT.exists_comp`, `NUPPT.exists_reparam`), and `exists_liftDistinguisher`
  the distinguisher for `π` at parameter `p(|x|)` from one for the pulled-back protocol at
  parameter `|x|` (`NUPPT.exists_reparam_advice` along a left inverse `φ` of `p.eval`, which
  exists because a syntactic polynomial with `p ≥ id` is strictly increasing,
  `polyExpr_strictMono_of_le`).

## Main definitions

* `TCSlib.Cryptography.LevinTransfer.coinTrunc`, `TCSlib.Cryptography.LevinTransfer.UnifProj`
  — truncation of coin strings and uniform projections of finite coin spaces.
* `TCSlib.Cryptography.LevinTransfer.liftVerifier`,
  `TCSlib.Cryptography.LevinTransfer.postView` — the verifier `V*'` and the view re-encoder of
  the zero-knowledge transfer (Claim-124.d).

## Main results

* `TCSlib.Cryptography.LevinTransfer.exec_congr` — executions with pointwise equal
  next-message functions coincide.
* `TCSlib.Cryptography.LevinTransfer.UnifProj.uprob_comp`,
  `TCSlib.Cryptography.LevinTransfer.distAdv_eq_of_unifProj` — events and distinguishing
  advantages are invariant under uniform projections of the coin spaces.
* `TCSlib.Cryptography.LevinTransfer.polyExpr_strictMono_of_le` — a syntactic polynomial
  dominating the identity is strictly increasing (hence injective).
* `TCSlib.Cryptography.LevinTransfer.liftVerifier_efficient`,
  `TCSlib.Cryptography.LevinTransfer.exists_liftSimulator`,
  `TCSlib.Cryptography.LevinTransfer.exists_liftDistinguisher`,
  `TCSlib.Cryptography.LevinTransfer.distinguisherL_lift` — the machines of the reduction
  and their functional equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, step 2.)
-/

namespace TCSlib.Cryptography.LevinTransfer

open Complexity Turing

/-! ### Executions with pointwise equal next-message functions -/

/-- Two executions whose next-message functions agree on every history — with possibly
different common inputs, auxiliary inputs and random tapes — have the same transcripts after
any number of moves (induction on the number of moves, `exec_succ`). This is the congruence
behind every "the pulled-back protocol on `x` is `π` on `f x`" step of Claim-124.d. -/
theorem exec_congr {P₁ V₁ P₂ V₂ : Strategy} {x₁ zP₁ zV₁ rP₁ rV₁ x₂ zP₂ zV₂ rP₂ rV₂ : List Bool}
    (hP : ∀ hist, P₁.next x₁ zP₁ rP₁ hist = P₂.next x₂ zP₂ rP₂ hist)
    (hV : ∀ hist, V₁.next x₁ zV₁ rV₁ hist = V₂.next x₂ zV₂ rV₂ hist) (vFirst : Bool) (k : ℕ) :
    exec P₁ V₁ vFirst x₁ zP₁ zV₁ rP₁ rV₁ k = exec P₂ V₂ vFirst x₂ zP₂ zV₂ rP₂ rV₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [exec_succ, exec_succ, ih]
    simp only [hP, hV]

/-! ### Coin truncation and uniform projections -/

/-- The first `m` bits of a coin string of length `M ≥ m`, as a typed coin string. -/
def coinTrunc {m M : ℕ} (h : m ≤ M) (r : Fin M → Bool) : Fin m → Bool := fun i => r (Fin.castLE h i)

/-- The list of a truncated coin string is the `take` of the list of the full string. -/
theorem ofFn_coinTrunc {m M : ℕ} (h : m ≤ M) (r : Fin M → Bool) :
    List.ofFn (coinTrunc h r) = (List.ofFn r).take m := by
  refine List.ext_getElem (by simp [h]) fun i h₁ h₂ => ?_
  simp [coinTrunc, List.getElem_take, List.getElem_ofFn]

/-- Truncating to the full length changes nothing (the typed cast of a coin string between
two coin spaces of equal size; the inequality `h` is a separate argument so that `rw` can
match it against the proof term found in the goal). -/
theorem ofFn_coinTrunc_of_eq {m M : ℕ} (h : m ≤ M) (h' : m = M) (r : Fin M → Bool) :
    List.ofFn (coinTrunc h r) = List.ofFn r := by
  rw [ofFn_coinTrunc, List.take_of_length_le (by simp [h'])]

/-- The bijection `{0,1}^M ≃ {0,1}^m × {0,1}^{M - m}` splitting a coin string at position
`m ≤ M` (`finSumFinEquiv`, `Equiv.sumArrowEquivProdArrow`). -/
def truncEquiv {m M : ℕ} (h : m ≤ M) : (Fin M → Bool) ≃ (Fin m → Bool) × (Fin (M - m) → Bool) :=
  (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl Bool)).trans
    ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow _ _ _))

/-- The first component of the splitting bijection is the truncation. -/
theorem truncEquiv_fst {m M : ℕ} (h : m ≤ M) (r : Fin M → Bool) :
    (truncEquiv h r).1 = coinTrunc h r := by
  funext i
  simp only [truncEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
    Equiv.symm_symm, finSumFinEquiv_apply_left, finCongr_symm, finCongr_apply, coinTrunc]
  congr 1

/-- A map `g : Ω → Ω'` between finite coin spaces is a **uniform projection** when it is the
first component of a bijection `Ω ≃ Ω' × K` with `K` nonempty: the image of the uniform
distribution on `Ω` under `g` is the uniform distribution on `Ω'`, the fibres being the
"independent padding" `K`. -/
def UnifProj {Ω Ω' : Type} (g : Ω → Ω') : Prop :=
  ∃ (K : Type) (_ : Fintype K) (_ : Nonempty K) (e : Ω ≃ Ω' × K), ∀ ω, (e ω).1 = g ω

/-- The law of an event is invariant under a uniform projection: `Pr_ω[q (g ω)] = Pr[q]`
(`uprob_comp_equiv` along the bijection, then `uprob_fst`). -/
theorem UnifProj.uprob_comp {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] {g : Ω → Ω'} (hg : UnifProj g)
    (q : Ω' → Prop) : uprob (fun ω => q (g ω)) = uprob q := by
  obtain ⟨K, _, _, e, he⟩ := hg
  have : (fun ω => q (g ω)) = fun ω => (fun z : Ω' × K => q z.1) (e ω) := by
    funext ω
    simp [he]
  rw [this]
  exact (uprob_comp_equiv e (fun z : Ω' × K => q z.1)).trans (uprob_fst q)

/-- Truncating a uniform coin string is a uniform projection (`truncEquiv`). -/
theorem unifProj_coinTrunc {m M : ℕ} (h : m ≤ M) : UnifProj (coinTrunc h) :=
  ⟨Fin (M - m) → Bool, inferInstance, inferInstance, truncEquiv h, truncEquiv_fst h⟩

/-- Uniform projections are closed under products (`Equiv.prodProdProdComm`). -/
theorem UnifProj.prod {Ω₁ Ω₁' Ω₂ Ω₂' : Type} {g₁ : Ω₁ → Ω₁'} {g₂ : Ω₂ → Ω₂'}
    (h₁ : UnifProj g₁) (h₂ : UnifProj g₂) : UnifProj (Prod.map g₁ g₂) := by
  obtain ⟨K₁, _, _, e₁, he₁⟩ := h₁
  obtain ⟨K₂, _, _, e₂, he₂⟩ := h₂
  refine ⟨K₁ × K₂, inferInstance, inferInstance,
    (Equiv.prodCongr e₁ e₂).trans (Equiv.prodProdProdComm Ω₁' K₁ Ω₂' K₂), fun ω => ?_⟩
  obtain ⟨ω₁, ω₂⟩ := ω
  simp [Equiv.prodProdProdComm, Prod.map, he₁, he₂]

/-- A distinguisher's acceptance probability is invariant under uniform projections of the
sampler's seed space and of its own coin space. -/
theorem acceptProb_comp_unifProj {σ σ' ρ ρ' γ : Type} [Fintype σ] [Fintype σ'] [Fintype ρ]
    [Fintype ρ'] (X : σ → γ) (D : γ → ρ → Bool) {gσ : σ' → σ} {gρ : ρ' → ρ}
    (hσ : UnifProj gσ) (hρ : UnifProj gρ) :
    acceptProb (fun s => X (gσ s)) (fun v r => D v (gρ r)) = acceptProb X D := by
  unfold acceptProb
  exact (hσ.prod hρ).uprob_comp (fun z : σ × ρ => D (X z.1) z.2 = true)

/-- Acceptance probabilities agree when the primed experiment is the unprimed one composed
with uniform projections: if `D' (X' s) r = D (X (gσ s)) (gρ r)` pointwise, then
`Pr[D'(X') = 1] = Pr[D(X) = 1]`. -/
theorem acceptProb_eq_of_unifProj {σ σ' ρ ρ' γ : Type} [Fintype σ] [Fintype σ'] [Fintype ρ]
    [Fintype ρ'] {X : σ → γ} {X' : σ' → γ} {D : γ → ρ → Bool} {D' : γ → ρ' → Bool}
    {gσ : σ' → σ} {gρ : ρ' → ρ} (hσ : UnifProj gσ) (hρ : UnifProj gρ)
    (hX : ∀ s r, D' (X' s) r = D (X (gσ s)) (gρ r)) : acceptProb X' D' = acceptProb X D := by
  rw [← acceptProb_comp_unifProj X D hσ hρ]
  unfold acceptProb
  congr 1
  funext z
  rw [hX]

/-- Distinguishing advantages agree when both samplers and the distinguisher of the primed
experiment are those of the unprimed one composed with uniform projections (the "padding is
uniform and independent" step of Claim-124.d). -/
theorem distAdv_eq_of_unifProj {σ σ' τ τ' ρ ρ' γ : Type} [Fintype σ] [Fintype σ'] [Fintype τ]
    [Fintype τ'] [Fintype ρ] [Fintype ρ'] {X : σ → γ} {X' : σ' → γ} {Y : τ → γ} {Y' : τ' → γ}
    {D : γ → ρ → Bool} {D' : γ → ρ' → Bool} {gσ : σ' → σ} {gτ : τ' → τ} {gρ : ρ' → ρ}
    (hσ : UnifProj gσ) (hτ : UnifProj gτ) (hρ : UnifProj gρ)
    (hX : ∀ s r, D' (X' s) r = D (X (gσ s)) (gρ r))
    (hY : ∀ t r, D' (Y' t) r = D (Y (gτ t)) (gρ r)) : distAdv X' Y' D' = distAdv X Y D := by
  unfold distAdv
  rw [acceptProb_eq_of_unifProj hσ hρ hX, acceptProb_eq_of_unifProj hτ hρ hY]

/-! ### Syntactic polynomials dominating the identity are strictly increasing -/

/-- A syntactic polynomial is either constant or strictly increasing.

**Proof sketch.** Induction on the expression. A constant is constant and the variable is
strictly increasing. A sum of two constants is constant, and a sum with at least one strictly
increasing summand is strictly increasing (`Nat.add_lt_add_left/right`, `Nat.add_lt_add`). A
product of two constants is constant; a constant times a strictly increasing function is
constant when the constant is `0` and strictly increasing otherwise
(`Nat.mul_lt_mul_of_pos_left/right`); a product of two strictly increasing functions with
values in `ℕ` is strictly increasing (`Nat.mul_lt_mul_of_lt_of_lt`). The power `p ^ 0` is
constant, and `p ^ (c + 1)` is constant or strictly increasing according to `p`
(`Nat.pow_lt_pow_left`). -/
theorem polyExpr_eval_const_or_strictMono (p : PolyExpr) :
    (∀ N, p.eval N = p.eval 0) ∨ StrictMono p.eval := by
  induction p with
  | const c => exact Or.inl fun _ => rfl
  | var => exact Or.inr strictMono_id
  | add p q hp hq =>
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl fun N => by simp only [PolyExpr.eval_add, hp N, hq N]
    · exact Or.inr fun a b h => by
        simp only [PolyExpr.eval_add, hp a, hp b]
        exact Nat.add_lt_add_left (hq h) _
    · exact Or.inr fun a b h => by
        simp only [PolyExpr.eval_add, hq a, hq b]
        exact Nat.add_lt_add_right (hp h) _
    · exact Or.inr fun a b h => Nat.add_lt_add (hp h) (hq h)
  | mul p q hp hq =>
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact Or.inl fun N => by simp only [PolyExpr.eval_mul, hp N, hq N]
    · by_cases h0 : p.eval 0 = 0
      · exact Or.inl fun N => by simp only [PolyExpr.eval_mul, hp N, h0, Nat.zero_mul]
      · exact Or.inr fun a b h => by
          simp only [PolyExpr.eval_mul, hp a, hp b]
          exact Nat.mul_lt_mul_of_pos_left (hq h) (Nat.pos_of_ne_zero h0)
    · by_cases h0 : q.eval 0 = 0
      · exact Or.inl fun N => by simp only [PolyExpr.eval_mul, hq N, h0, Nat.mul_zero]
      · exact Or.inr fun a b h => by
          simp only [PolyExpr.eval_mul, hq a, hq b]
          exact Nat.mul_lt_mul_of_pos_right (hp h) (Nat.pos_of_ne_zero h0)
    · exact Or.inr fun a b h => Nat.mul_lt_mul_of_lt_of_lt (hp h) (hq h)
  | pow p c hp =>
    cases c with
    | zero => exact Or.inl fun N => by simp [PolyExpr.eval_pow]
    | succ c =>
      rcases hp with hp | hp
      · exact Or.inl fun N => by simp only [PolyExpr.eval_pow, hp N]
      · exact Or.inr fun a b h => Nat.pow_lt_pow_left (hp h) (Nat.succ_ne_zero c)

/-- A syntactic polynomial dominating the identity is strictly increasing (it is not constant,
since `p(p(0) + 1) ≥ p(0) + 1 > p(0)`), hence injective: the length polynomial of a Levin
reduction has a left inverse, along which the distinguisher of the zero-knowledge transfer is
re-parametrized. -/
theorem polyExpr_strictMono_of_le {p : PolyExpr} (hp : ∀ N, N ≤ p.eval N) : StrictMono p.eval := by
  rcases polyExpr_eval_const_or_strictMono p with h | h
  · exfalso
    have := hp (p.eval 0 + 1)
    rw [h (p.eval 0 + 1)] at this
    omega
  · exact h

/-! ### The verifier `V*'` of the zero-knowledge transfer -/

/-- The verifier `V*'` for `π` built from a verifier `V'` of the pulled-back protocol
[PS10, §4.7, Theorem 124.1, step 2] (Claim-124.d, zero-knowledge half): it recovers the
original instance `x` and auxiliary input `z` from its auxiliary input `⟨x, z⟩`, ignores the
common input `x' = f x`, and runs `V'` on the first `V'.coinLen |x|` bits of its random tape.
Its coin polynomial is `V'.coins`, so at `|x'| = p(|x|) ≥ |x|` the tape is long enough
(`PolyExpr.eval_mono`). -/
def liftVerifier (V' : Strategy) : Strategy where
  next _ z' r hist :=
    V'.next (pairFstD z') (pairSndD z') (r.take (V'.coinLen (pairFstD z').length)) hist
  coins := V'.coins

/-- The next-message function of `liftVerifier V'` on the auxiliary input `⟨x, z⟩`. -/
theorem liftVerifier_next (V' : Strategy) (x' x z r : List Bool) (hist : List (List Bool)) :
    (liftVerifier V').next x' (pairEncode x z) r hist =
      V'.next x z (r.take (V'.coinLen x.length)) hist := by
  simp [liftVerifier]

/-- The coin length of `liftVerifier V'` is that of `V'`. -/
theorem liftVerifier_coinLen (V' : Strategy) (n : ℕ) :
    (liftVerifier V').coinLen n = V'.coinLen n := rfl

/-- `liftVerifier V'` is efficient when `V'` is.

**Proof sketch.** From `hV'` take the uniform `A` with `V'.next x z r hist =
A.runAtL |x| ⟨⟨x, z⟩, msgs⟩ r`. On the raw layout `⟨⟨⟨1^{|x'|}, ⟨⟨x', ⟨x, z⟩⟩, msgs⟩⟩, []⟩, r⟩`
the function `⟨x, z⟩ ↦ A.output ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r.take (A.coins |x|)⟩` is
polynomial-time: the slots are projection chains (`NUPPT.inArg`, `NUPPT.inCoins`, `pairFstD`,
`pairSndD`), `1^{|x|}` is `Complexity.polyTimeComputable_unary`, the cut is
`Complexity.polyTimeComputable_pairTakePoly A.coins` on `⟨x, r⟩`, the layout is
`NUPPT.polyTimeComputable_layout` and the machine `NUPPT.polyTimeComputable_output`.
`NUPPT.ofPolyTimeUniform` of it with coins `A.coins = V'.coins` is uniform and computes
`liftVerifier V'` (`NUPPT.runAtL_ofPolyTimeUniform`, `NUPPT.runAtL_eq_output_layout`, the
advice of `A` being empty). -/
theorem liftVerifier_efficient {V' : Strategy} (hV' : V'.Efficient) :
    (liftVerifier V').Efficient := by
  obtain ⟨A, hA, hc, hnext⟩ := hV'
  have hz' : PolyTimeComputable fun L => pairSndD (pairFstD (NUPPT.inArg L)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)
  have hxx : PolyTimeComputable fun L => pairFstD (pairSndD (pairFstD (NUPPT.inArg L))) :=
    polyTimeComputable_pairFstD.comp hz'
  have hzz : PolyTimeComputable fun L => pairSndD (pairSndD (pairFstD (NUPPT.inArg L))) :=
    polyTimeComputable_pairSndD.comp hz'
  have hm : PolyTimeComputable fun L => pairSndD (NUPPT.inArg L) :=
    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hu : PolyTimeComputable fun L =>
      List.replicate (pairFstD (pairSndD (pairFstD (NUPPT.inArg L)))).length true :=
    polyTimeComputable_unary.comp hxx
  have htake : PolyTimeComputable fun L =>
      (NUPPT.inCoins L).take (A.coins.eval (pairFstD (pairSndD (pairFstD (NUPPT.inArg L)))).length) := by
    convert (polyTimeComputable_pairTakePoly A.coins).comp
      (hxx.pairEncode NUPPT.polyTimeComputable_inCoins) using 1
    funext L
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hF := A.polyTimeComputable_output.comp
    (NUPPT.polyTimeComputable_layout hu ((hxx.pairEncode hzz).pairEncode hm)
      (polyTimeComputable_const []) htake)
  refine ⟨NUPPT.ofPolyTimeUniform hF A.coins, NUPPT.ofPolyTimeUniform_uniform hF _, hc,
    fun x' z' r hist => ?_⟩
  rw [Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform]
  show V'.next _ _ _ _ = _
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA]
  simp only [Function.comp_apply, NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput, NUPPT.layout,
    pairFstD_pairEncode, pairSndD_pairEncode, Strategy.coinLen, hc]

/-! ### Re-encoding views -/

/-- The view re-encoder of the zero-knowledge transfer: a view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩` of
`V*' = liftVerifier V'` in `π` becomes the view `⟨⟨x, z⟩, ⟨r'.take (c |x|), msgs⟩⟩` of `V'` in
the pulled-back protocol, where `c = V'.coins` (the simulator for `V'` is `postView` of the
simulator for `V*'`, and the distinguisher for `V*'` is the one for `V'` after `postView`). -/
def postView (c : PolyExpr) (v : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD v))
    (pairEncode ((pairFstD (pairSndD v)).take (c.eval (pairFstD (pairSndD (pairFstD v))).length))
      (pairSndD (pairSndD v)))

/-- `postView` on an encoded view with auxiliary input `⟨x, z⟩`. -/
theorem postView_encode (c : PolyExpr) (x' x z r' : List Bool) (msgs : List (List Bool)) :
    postView c (View.encode ⟨x', pairEncode x z, r', msgs⟩) =
      View.encode ⟨x, z, r'.take (c.eval x.length), msgs⟩ := by
  simp [postView, View.encode]

/-- `postView c` is polynomial-time (projection chains, `polyTimeComputable_pairTakePoly c`
on `⟨x, r'⟩`, `PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_postView (c : PolyExpr) : PolyTimeComputable (postView c) := by
  have h1 : PolyTimeComputable fun v => pairSndD (pairFstD v) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hx : PolyTimeComputable fun v => pairFstD (pairSndD (pairFstD v)) :=
    polyTimeComputable_pairFstD.comp h1
  have hr : PolyTimeComputable fun v => pairFstD (pairSndD v) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun v => pairSndD (pairSndD v) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have htake : PolyTimeComputable fun v =>
      (pairFstD (pairSndD v)).take (c.eval (pairFstD (pairSndD (pairFstD v))).length) := by
    convert (polyTimeComputable_pairTakePoly c).comp (hx.pairEncode hr) using 1
    funext v
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  exact h1.pairEncode (htake.pairEncode hm)

/-! ### The simulator and the distinguisher of the zero-knowledge transfer -/

/-- **The simulator for `V'` from the simulator for `V*'`** (Claim-124.d): for a machine `S'`
(the simulator for `liftVerifier V'` in `π`), a polynomial-time `f` and polynomials `c`, `p`,
there is a machine `S` with coins `S'.coins.subst p`, uniform when `S'` is, with
`S(1^n, y; r) = postView c (S'(1^{p n}, ⟨f (fst y), y⟩; r))` — on `y = ⟨x, z⟩` this is
`postView` of `S'` run on `(f x, ⟨x, z⟩)` at parameter `p(|x|) = |f x|`
(`NUPPT.exists_comp` with `pre y := ⟨f (fst y), y⟩`, `post := postView c`, then
`NUPPT.exists_reparam p`). -/
theorem exists_liftSimulator (S' : NUPPT) {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (c p : PolyExpr) :
    ∃ S : NUPPT, S.coins = S'.coins.subst p ∧ (S'.Uniform → S.Uniform) ∧
      ∀ n y r, S.runAtL n y r = postView c (S'.runAtL (p.eval n) (pairEncode (f (pairFstD y)) y) r) := by
  obtain ⟨B, hBc, -, hBadv, hB⟩ := S'.exists_comp
    ((hf.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_id)
    (polyTimeComputable_postView c)
  obtain ⟨S, hSc, hSu, hS⟩ := B.exists_reparam p
  refine ⟨S, by rw [hSc, hBc], fun hu => hSu fun n => by rw [hBadv]; exact hu n, fun n y r => ?_⟩
  rw [hS, hB]
  rfl

/-- **The distinguisher for `π` from the distinguisher for the pulled-back protocol**
(Claim-124.d): for a machine `D`, a map `φ` with `φ n ≤ n` (a left inverse of the length
polynomial) and a polynomial `c`, there is a machine `D'` with `D`'s coins such that
`D'(1^n, v; r) = D(1^{φ n}, postView c v; r.take (D.coinLen (φ n)))`
(`NUPPT.exists_reparam_advice` along `φ` with majorant `var`, then `NUPPT.exists_comp` with
`pre := postView c`). -/
theorem exists_liftDistinguisher (D : NUPPT) (φ : ℕ → ℕ) (hφ : ∀ n, φ n ≤ n) (c : PolyExpr) :
    ∃ D' : NUPPT, D'.coins = D.coins ∧
      ∀ n y r, D'.runAtL n y r = D.runAtL (φ n) (postView c y) (r.take (D.coinLen (φ n))) := by
  obtain ⟨B, hBc, hB⟩ := D.exists_reparam_advice φ .var hφ
  obtain ⟨D', hDc, -, -, hD'⟩ := B.exists_comp (polyTimeComputable_postView c) polyTimeComputable_id
  refine ⟨D', by rw [hDc, hBc, PolyExpr.subst_var], fun n y r => ?_⟩
  rw [hD', hB]
  rfl

/-- The verdict of the lifted distinguisher at parameter `n` with `φ n = m` is the verdict of
`D` at parameter `m` on the re-encoded sample with the truncated coins
(`NUPPT.distinguisherL`, `ofFn_coinTrunc`). -/
theorem distinguisherL_lift {D D' : NUPPT} {φ : ℕ → ℕ} {c : PolyExpr}
    (hD' : ∀ n y r, D'.runAtL n y r = D.runAtL (φ n) (postView c y) (r.take (D.coinLen (φ n))))
    {n m : ℕ} (hφn : φ n = m) (hle : D.coinLen m ≤ D'.coinLen n) (v : List Bool)
    (ρ : D'.Coins n) :
    D'.distinguisherL n v ρ = D.distinguisherL m (postView c v) (coinTrunc hle ρ) := by
  simp only [NUPPT.distinguisherL, NUPPT.runAt_eq, hD', hφn, ofFn_coinTrunc]

end TCSlib.Cryptography.LevinTransfer
