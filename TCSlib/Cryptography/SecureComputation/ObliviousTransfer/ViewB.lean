/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oblivious transfer: Bob's side of Proposition 161.5

Bob's real view of Protocol 160.4 differs from `S_B`'s only in the unselected mask:
`z_{1−b} = h(f_i⁻¹(y_{1−b})) ⊕ a_{1−b}` in the real view, a fresh coin in the simulated one
[PS10, Proposition 161.5, the proof left as an exercise]. Both are `OT.bobView` with the
unselected mask `β ⊕ a_{1−b}`, where `β = h(f_i⁻¹(y_{1−b}))` (real) or `β` is uniform
(simulated). Writing `P(β)` for `D`'s acceptance probability, the real one is `E_r P(B)`, the
simulated one `E_r (P(B) + P(¬B))/2`, so the advantage is `|E_r P(B) − E_r P(¬B)| / 2`. The
signed predictor (`uprob_signedPredictor_false`, `_true`) run on the view-building distinguisher
`D'` (`OT.viewDist`) predicts `B` from `⟨i, s'⟩` with probability `1/2 ± (P(B) − P(¬B))/2`, so the
enhanced hard-core hypothesis bounds the advantage by `|ε_false(n)| + |ε_true(n)|` for the fixed
bits `(b, a₀, a₁)`. The eight choices of these bits give sixteen machines; the sum of their
bounds is negligible and uniform over the inputs.

## Main definitions

* `OT.hcBit`: the enhanced hard-core bit `h_i(f_i⁻¹(Sample(i; s)))` of a sampled element.
* `OT.accB`: `D`'s acceptance probability of Bob's view with a given unselected bit.

## Main results

* `OT.uprob_signedPredictor_false`, `OT.uprob_signedPredictor_true`: the signed-predictor
  identity of Algorithm 104.3's proof for a uniform challenge `x` and a bit `B x`.
* `OT.uprob_xor_shear`, `OT.negligible_finset_sum`: a uniform bit masked by a fixed bit, and
  finite sums of negligible functions.
* `OT.mask_eval`, `OT.mask_raw`: Alice's two masks on Bob's real pair.
* `OT.realB_realCoins`, `OT.idealB_simBCoins`: Bob's real and ideal samplers on typed coins;
  `OT.acceptProb_realB`, `OT.acceptProb_idealB`: their acceptance probabilities through `accB`.
* `OT.acceptProb_viewDist`, `OT.uprob_predictor_false`, `OT.uprob_predictor_true`: the
  prediction experiments of the two predictors.
* `OT.distAdv_realB_idealB_le`, `OT.exists_negligible_bob`: the bound on Bob's side.
* `OT.simulators_of_isOT`: Proposition 161.5 with its simulators, for every protocol and pair of
  machines of the shapes of Protocol 160.4 and of `S_A`, `S_B`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.4, Proposition 161.5, and Theorem 104.4 (the predictor), book pp. 104, 161–162.
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3.2 (the enhanced predicate in the OT argument).
-/

namespace TCSlib.Cryptography.SecureComputation.OT

open Complexity Turing TCSlib.Cryptography

variable (T : TrapdoorCollection) (H : List Bool → List Bool)

/-! ### The signed predictor -/

/-- **The signed predictor, unflipped** (the identity behind [PS10, Theorem 104.4, proof], for a
uniform challenge `x` and a bit `B x`): drawing `c` and coins `ρ`, outputting `c` if `D(x, c; ρ)`
accepts and `¬c` otherwise, predicts `B x` with probability
`1/2 + (Pr[D(x, B x) = 1] − Pr[D(x, ¬B x) = 1]) / 2`.

**Proof sketch.** Substitute `c = d ⊕ B x` (a bijection of `Bool × (α × ρ)`) and split on `d`
(`uprob_bool_prod`): for `d = 0` the prediction is right iff `D(x, B x)` accepts, for `d = 1` iff
`D(x, ¬B x)` rejects (`uprob_not`). -/
theorem uprob_signedPredictor_false {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α]
    [Nonempty ρ] (B : α → Bool) (D : α × Bool → ρ → Bool) :
    uprob (fun z : α × (Bool × ρ) =>
        xor (if D (z.1, z.2.1) z.2.2 then z.2.1 else !z.2.1) false = B z.1) =
      1 / 2 + (acceptProb (fun x => (x, B x)) D - acceptProb (fun x => (x, !B x)) D) / 2 := by
  let e : Bool × (α × ρ) ≃ α × (Bool × ρ) :=
    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
      left_inv := fun v => by simp
      right_inv := fun z => by simp }
  rw [← uprob_comp_equiv e, uprob_bool_prod, acceptProb_def, acceptProb_def,
    show ∀ a b : ℝ, 1 / 2 + (a - b) / 2 = (a + (1 - b)) / 2 by intro a b; ring, ← uprob_not]
  congr 2
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.false_xor, Bool.xor_false]
    cases D (w.1, B w.1) w.2 <;> cases B w.1 <;> simp
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.true_xor, Bool.xor_false]
    cases D (w.1, !B w.1) w.2 <;> cases B w.1 <;> simp

/-- **The signed predictor, flipped**: the same predictor negated predicts `B x` with probability
`1/2 − (Pr[D(x, B x) = 1] − Pr[D(x, ¬B x) = 1]) / 2`.

**Proof sketch.** As `uprob_signedPredictor_false`: substitute `c = d ⊕ B x` and split on `d`.
With the output negated, for `d = 0` the prediction is right iff `D(x, B x)` rejects
(`uprob_not`), and for `d = 1` iff `D(x, ¬B x)` accepts. -/
theorem uprob_signedPredictor_true {α ρ : Type*} [Fintype α] [Fintype ρ] [Nonempty α]
    [Nonempty ρ] (B : α → Bool) (D : α × Bool → ρ → Bool) :
    uprob (fun z : α × (Bool × ρ) =>
        xor (if D (z.1, z.2.1) z.2.2 then z.2.1 else !z.2.1) true = B z.1) =
      1 / 2 - (acceptProb (fun x => (x, B x)) D - acceptProb (fun x => (x, !B x)) D) / 2 := by
  let e : Bool × (α × ρ) ≃ α × (Bool × ρ) :=
    { toFun := fun v => (v.2.1, (xor v.1 (B v.2.1), v.2.2))
      invFun := fun z => (xor z.2.1 (B z.1), (z.1, z.2.2))
      left_inv := fun v => by simp
      right_inv := fun z => by simp }
  rw [← uprob_comp_equiv e, uprob_bool_prod, acceptProb_def, acceptProb_def,
    show ∀ a b : ℝ, 1 / 2 - (a - b) / 2 = ((1 - a) + b) / 2 by intro a b; ring, ← uprob_not]
  congr 2
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.false_xor, Bool.xor_true]
    cases D (w.1, B w.1) w.2 <;> cases B w.1 <;> simp
  · congr 1
    funext w
    apply propext
    simp only [e, Equiv.coe_fn_mk, Bool.true_xor, Bool.xor_true]
    cases D (w.1, !B w.1) w.2 <;> cases B w.1 <;> simp

/-- **A uniform bit masked by a fixed bit, re-centred on `g x`**: over uniform `(β, x)`,
`Pr[Q (β ⊕ a) x] = (Pr[Q (g x) x] + Pr[Q (¬g x) x]) / 2` (the bijection `β ↦ β ⊕ a ⊕ g x`, then
`uprob_bool_prod`). -/
theorem uprob_xor_shear {X : Type*} [Fintype X] (g : X → Bool) (a : Bool) (Q : Bool → X → Prop) :
    uprob (fun w : Bool × X => Q (xor w.1 a) w.2) =
      (uprob (fun x => Q (g x) x) + uprob (fun x => Q (!g x) x)) / 2 := by
  let e : Bool × X ≃ Bool × X :=
    { toFun := fun w => (xor (xor w.1 (g w.2)) a, w.2)
      invFun := fun w => (xor (xor w.1 a) (g w.2), w.2)
      left_inv := fun w => by simp
      right_inv := fun w => by simp }
  rw [← uprob_comp_equiv e, uprob_bool_prod]
  congr 2 <;> congr 1 <;> funext x <;> simp only [e, Equiv.coe_fn_mk] <;> cases g x <;>
    cases a <;> rfl

/-- **A finite sum of negligible functions is negligible** (`Negligible.add` by induction on the
finite set): `(∀ i ∈ s, Negligible (f i)) → Negligible (fun n => ∑ i ∈ s, f i n)`. -/
theorem negligible_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → ℝ}
    (h : ∀ i ∈ s, Negligible (f i)) : Negligible fun n => ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using negligible_zero
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-! ### The enhanced bit and the two masks -/

/-- **The enhanced hard-core bit of a sampled element** [Gol04, §7.3.2]: at the index
`i = index n r`, `hcBit T h n r s = h_i(perm_i⁻¹(dec_i(Sample(i; s))))`. -/
def hcBit (h : ∀ i, T.D i → Bool) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) : Bool :=
  h (T.index n r) ((T.perm (T.index n r)).symm
    ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default))

/-- The defining equation of `hcBit`: `hcBit T h n r s =
h_i (perm_i⁻¹ ((dec_i (Sample(i; s))).getD default))` with `i = index n r`. -/
theorem hcBit_eq (h : ∀ i, T.D i → Bool) (n : ℕ) (r : T.gen.Coins n) (s : T.sample.Coins n) :
    hcBit T h n r s = h (T.index n r) ((T.perm (T.index n r)).symm
      ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) s)).getD default)) := rfl

/-- **The inverter on the all-`true` tape** [PS10, Definition 56.1 (6)]:
`Inv(1^n, ⟨t, encD y⟩; 1^{inv(n)}) = encD (perm⁻¹ y)` (`TrapdoorCollection.inv_eq_encD`). -/
theorem inv_runAtL_ones (n : ℕ) (r : T.gen.Coins n) (y : T.D (T.index n r)) :
    T.inv.runAtL n (pairEncode (T.trap n r) (T.encD _ y))
        (List.replicate (T.inv.coins.eval n) true) =
      T.encD _ ((T.perm _).symm y) := by
  rw [← NUPPT.coinLen_eq, ← List.ofFn_const, ← NUPPT.runAt_eq]
  exact T.inv_eq_encD n r y fun _ => true

/-- **The selected mask** [PS10, Protocol 160.4]: on `y_b = eval ⟨i, w⟩` with `w = Sample(i; s)`,
Alice's mask is `H ⟨i, w⟩ ⊕ [c]` (the inverter returns `w`'s element, `H` is correct on it). -/
theorem mask_eval {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) (n : ℕ)
    (r : T.gen.Coins n) (s : T.sample.Coins n) (c : Bool) :
    mask T H n (T.index n r) (T.trap n r)
        (T.eval (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s))) c =
      List.zipWith xor (H (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s))) [c] := by
  obtain ⟨x, hx, hev⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
  have hw : H (pairEncode (T.index n r) (T.sample.runAt n (T.index n r) s)) = [h _ x] :=
    T.toCollection.apply_of_decD (v := fun i x => [h i x]) henc hx
  rw [mask_eq, hev, T.f_perm, inv_runAtL_ones, Equiv.symm_apply_apply, henc, hw]

/-- **The unselected mask** [PS10, Protocol 160.4]: on the raw sample `w' = Sample(i; s)`,
Alice's mask is `[hcBit T h n r s ⊕ c]` (the inverter returns the encoding of
`perm⁻¹(dec w')`). -/
theorem mask_raw {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) (n : ℕ)
    (r : T.gen.Coins n) (s : T.sample.Coins n) (c : Bool) :
    mask T H n (T.index n r) (T.trap n r) (T.sample.runAt n (T.index n r) s) c =
      [xor (hcBit T h n r s) c] := by
  obtain ⟨x, hx, -⟩ := (Collection.evalSampled_iff _).1 T.toCollection.evalSampled n r s
  have hw : T.sample.runAt n (T.index n r) s = T.encD _ x :=
    (Collection.decD_eq_some_iff _).1 hx
  rw [mask_eq, hcBit_eq, hx, Option.getD_some, hw, inv_runAtL_ones, henc]
  rfl

/-! ### Bob's real and ideal samplers -/

/-- Alice's input string is the two-bit list `[a₀, a₁]`:
`List.ofFn (inA2 a) = [inA2 a 0, inA2 a 1]`. -/
theorem ofFn_inA2_eq {n : ℕ} (a : Fin (otFunctionality.inA.eval n) → Bool) :
    List.ofFn (inA2 a) = [inA2 a 0, inA2 a 1] := by
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

/-- **Bob's real sampler on typed coins**: on `(r, s₁, s₂)` (`realCoins`) it is
`bobView (1^n) b a₀ a₁ i (s₁ ++ s₂) (Sample(i; s₁)) (hcBit T h n r s₂)` with `i = index n r`.

**Proof sketch.** Unfold the real sampler to the transcript (`transcriptWith_isOT`) on the
assembled tapes (`realCoins_symm_fst_ofFn`, `realCoins_symm_snd_ofFn`), with Alice's output `[]`
(`houtP`). Then cases on `b`: the selected mask is `mask_eval`, the unselected one `mask_raw`. -/
theorem realB_realCoins {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × T.sample.Coins n)) :
    otFunctionality.realB π n a b ((realCoins T H hπ n).symm p) =
      bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1) (T.index n p.1)
        (List.ofFn p.2.1 ++ List.ofFn p.2.2) (T.sample.runAt n (T.index n p.1) p.2.1)
        (hcBit T h n p.1 p.2.2) := by
  have hlen : (List.ofFn p.2.1).length = T.sample.coins.eval n := length_ofFn_coins _ n _
  rw [Functionality.realB_eq, Protocol.viewV_eq, View.encode_mk, transcriptWith_isOT T H hπ,
    ← ofFn_inA2 a, ← ofFn_inB1 b, houtP, ofFn_inB1, ofFn_eq_inB1, ofFn_inA2_eq,
    realCoins_symm_fst_ofFn, realCoins_symm_snd_ofFn, senderNext_single, receiverNext_single,
    List.length_replicate, List.take_left' hlen, List.drop_left' hlen, List.headD_cons,
    ← NUPPT.runAt_eq, ← NUPPT.runAt_eq, ← NUPPT.runAt_eq, ← Collection.index_eq,
    ← Collection.trap_eq, Strategy.encodeMsgs_cons, Strategy.encodeMsgs_cons,
    Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil, bobView_eq]
  cases inB1 b 0
  · simp only [Bool.false_eq_true, if_false, pairFstD_pairEncode, pairSndD_pairEncode,
      mask_eval T H henc, mask_raw T H henc, List.getD_cons_zero, List.getD_cons_succ]
  · simp only [if_true, pairFstD_pairEncode, pairSndD_pairEncode,
      mask_eval T H henc, mask_raw T H henc, List.getD_cons_zero, List.getD_cons_succ]

/-- **Bob's ideal sampler on typed coins**: on `(r, s₁, s₂, c)` (`simBCoins`) it is
`bobView (1^n) b a₀ a₁ i (s₁ ++ s₂) (Sample(i; s₁)) (c ⊕ a_{1−b})` with `i = index n r`. -/
theorem idealB_simBCoins {S : NUPPT} (hS : IsSimB T H S) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
    (p : T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) :
    otFunctionality.idealB S n a b ((simBCoins T H hS n).symm p) =
      bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1) (T.index n p.1)
        (List.ofFn p.2.1 ++ List.ofFn p.2.2.1) (T.sample.runAt n (T.index n p.1) p.2.1)
        (xor (p.2.2.2 0) (if inB1 b 0 then inA2 a 0 else inA2 a 1)) := by
  have hc : List.ofFn p.2.2.2 = [p.2.2.2 0] := by rw [List.ofFn_succ, List.ofFn_zero]
  rw [Functionality.idealB_eq, ((isSimB_iff T H S).1 hS).2, simBCoins_symm_ofFn, simBView_layout,
    pairFstD_pairEncode, pairSndD_pairEncode, ofFn_f_snd, ofFn_f_fst, ofFn_eq_inB1,
    List.headD_cons, hc, bobView_eq]
  cases inB1 b 0 <;> simp

/-! ### Acceptance probabilities -/

/-- `D`'s acceptance probability of Bob's view at the index of `r` with the unselected bit
`g(s₂)`: `accB T H D n b a₀ a₁ r g = Pr_{s₁, s₂, ρ}[D(bobView … (s₁ ++ s₂) (Sample(i; s₁))
(g s₂); ρ) = 1]`. -/
noncomputable def accB (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n)
    (g : T.sample.Coins n → Bool) : ℝ :=
  uprob fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n =>
    D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ (T.index n r)
      (List.ofFn q.1.1 ++ List.ofFn q.1.2) (T.sample.runAt n (T.index n r) q.1.1) (g q.1.2))
      q.2 = true

/-- The defining equation of `accB`: `accB T H D n b a₀ a₁ r g =
Pr_{((s₁, s₂), ρ)}[D(bobView … (s₁ ++ s₂) (Sample(i; s₁)) (g s₂); ρ) = 1]`. -/
theorem accB_eq (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n)
    (g : T.sample.Coins n → Bool) :
    accB T H D n b a₀ a₁ r g =
      uprob fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n =>
        D.distinguisherL n (bobView H (List.replicate n true) b a₀ a₁ (T.index n r)
          (List.ofFn q.1.1 ++ List.ofFn q.1.2) (T.sample.runAt n (T.index n r) q.1.1) (g q.1.2))
          q.2 = true := rfl

/-- **Bob's real acceptance** is the average over `Gen`'s coins of `accB` with the enhanced bit:
`acceptProb realB D = E_r accB … r (hcBit T h n r)`. -/
theorem acceptProb_realB {h : ∀ i, T.D i → Bool}
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    (D : NUPPT) (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    acceptProb (otFunctionality.realB π n a b) (D.distinguisherL n) =
      uexp fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) := by
  rw [← acceptProb_comp_equiv (realCoins T H hπ n).symm, acceptProb_def]
  simp only [realB_realCoins T H henc hπ houtP]
  rw [← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm, uprob_prod]
  congr 1

/-- **Bob's ideal acceptance** is the average of the two `accB` with the enhanced bit and its
negation: `acceptProb idealB D = E_r (accB … r B + accB … r ¬B) / 2`.

**Proof sketch.** Relabel the coins as `(r, s₁, s₂, c)` (`simBCoins`, `idealB_simBCoins`), reorder
them as `(r, (c₀, ((s₁, s₂), ρ)))` by an explicit bijection `E` (`c` read as its bit `c₀`), average
over `r` (`uprob_prod`), and apply `uprob_xor_shear` to the unselected bit `c₀ ⊕ a_{1−b}`,
re-centred on `B(s₂)`. -/
theorem acceptProb_idealB {h : ∀ i, T.D i → Bool} {S : NUPPT} (hS : IsSimB T H S) (D : NUPPT)
    (n : ℕ) (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool) :
    acceptProb (otFunctionality.idealB S n a b) (D.distinguisherL n) =
      uexp fun r => (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) / 2 := by
  let E : T.gen.Coins n × (Bool × ((T.sample.Coins n × T.sample.Coins n) × D.Coins n)) ≃
      (T.gen.Coins n × (T.sample.Coins n × (T.sample.Coins n × (Fin 1 → Bool)))) × D.Coins n :=
    { toFun := fun w => ((w.1, (w.2.2.1.1, (w.2.2.1.2, fun _ => w.2.1))), w.2.2.2)
      invFun := fun z => (z.1.1, (z.1.2.2.2 0, ((z.1.2.1, z.1.2.2.1), z.2)))
      left_inv := fun w => rfl
      right_inv := fun z => by
        obtain ⟨⟨r, s₁, s₂, c⟩, ρ⟩ := z
        refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun j => ?_)))) rfl
        rw [Subsingleton.elim j 0] }
  rw [← acceptProb_comp_equiv (simBCoins T H hS n).symm, acceptProb_def]
  simp only [idealB_simBCoins T H hS]
  rw [← uprob_comp_equiv E, uprob_prod]
  congr 1
  funext r
  simp only [E, Equiv.coe_fn_mk]
  rw [accB_eq, accB_eq]
  have key := uprob_xor_shear
    (fun q : (T.sample.Coins n × T.sample.Coins n) × D.Coins n => hcBit T h n r q.1.2)
    (if inB1 b 0 then inA2 a 0 else inA2 a 1) fun β q =>
      D.distinguisherL n (bobView H (List.replicate n true) (inB1 b 0) (inA2 a 0) (inA2 a 1)
        (T.index n r) (List.ofFn q.1.1 ++ List.ofFn q.1.2)
        (T.sample.runAt n (T.index n r) q.1.1) β) q.2 = true
  exact key

/-! ### The predictor machines -/

/-- **`D'`'s acceptance on `⟨i, ⟨s', [g s']⟩⟩` is `accB`**: over uniform `s'` and `D'`'s coins,
`D'` accepts `⟨i, ⟨s', [g s']⟩⟩` with probability `accB T H D n b a₀ a₁ r g` (`viewDistCoins`,
`distinguisherL_viewDist`, and the reordering `(s₂, (s₁, ρ)) ↦ ((s₁, s₂), ρ)`):
`acceptProb (fun x => (x, g x)) (fun yc ρ => D'.distinguisherL n ⟨i, ⟨ofFn yc.1, [yc.2]⟩⟩ ρ) =
accB T H D n b a₀ a₁ r g` with `D' = viewDist T hH D b a₀ a₁` and `i = T.index n r`. -/
theorem acceptProb_viewDist (hH : PolyTimeComputable H) (D : NUPPT) (n : ℕ) (b a₀ a₁ : Bool)
    (r : T.gen.Coins n) (g : T.sample.Coins n → Bool) :
    acceptProb (fun x : T.sample.Coins n => (x, g x))
        (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
          (viewDist T hH D b a₀ a₁).distinguisherL n
            (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ) =
      accB T H D n b a₀ a₁ r g := by
  let e : (T.sample.Coins n × T.sample.Coins n) × D.Coins n ≃
      T.sample.Coins n × (viewDist T hH D b a₀ a₁).Coins n :=
    { toFun := fun q => (q.1.2, (viewDistCoins T hH D b a₀ a₁ n).symm (q.1.1, q.2))
      invFun := fun z => ((((viewDistCoins T hH D b a₀ a₁ n) z.2).1, z.1),
        ((viewDistCoins T hH D b a₀ a₁ n) z.2).2)
      left_inv := fun q => by simp
      right_inv := fun z => by simp }
  rw [acceptProb_def, accB_eq, ← uprob_comp_equiv e]
  congr 1
  funext q
  simp only [e, Equiv.coe_fn_mk]
  rw [distinguisherL_viewDist]

/-- **The unflipped predictor's prediction experiment** at the index of `r`: the machine
`tdpPredictor D' false` predicts `hcBit T h n r s'` from `⟨i, s'⟩` with probability
`1/2 + (accB … r B − accB … r ¬B) / 2` (`uprob_tdpPredictor`, `uprob_signedPredictor_false`,
`acceptProb_viewDist`): `uprob (fun z => P.distinguisherL n ⟨T.index n r, ofFn z.1⟩ z.2 = B z.1) =
1 / 2 + (accB T H D n b a₀ a₁ r B - accB T H D n b a₀ a₁ r (fun s => !B s)) / 2` with
`P = tdpPredictor (viewDist T hH D b a₀ a₁) false` and `B = hcBit T h n r`. -/
theorem uprob_predictor_false (h : ∀ i, T.D i → Bool) (hH : PolyTimeComputable H) (D : NUPPT)
    (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n) :
    uprob (fun z : T.sample.Coins n × (tdpPredictor (viewDist T hH D b a₀ a₁) false).Coins n =>
        (tdpPredictor (viewDist T hH D b a₀ a₁) false).distinguisherL n
          (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) =
      1 / 2 + (accB T H D n b a₀ a₁ r (hcBit T h n r) -
        accB T H D n b a₀ a₁ r (fun s => !hcBit T h n r s)) / 2 := by
  have h₁ := uprob_tdpPredictor (viewDist T hH D b a₀ a₁) false n (T.index n r)
    (id : T.sample.Coins n → T.sample.Coins n) (hcBit T h n r) List.ofFn
  have h₂ := uprob_signedPredictor_false (hcBit T h n r)
    (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
      (viewDist T hH D b a₀ a₁).distinguisherL n
        (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ)
  rw [acceptProb_viewDist T H hH D n b a₀ a₁ r (hcBit T h n r),
    acceptProb_viewDist T H hH D n b a₀ a₁ r (fun s => !hcBit T h n r s)] at h₂
  exact h₁.trans h₂

/-- **The flipped predictor's prediction experiment**: `tdpPredictor D' true` predicts
`hcBit T h n r s'` with probability `1/2 − (accB … r B − accB … r ¬B) / 2`:
`uprob (fun z => P.distinguisherL n ⟨T.index n r, ofFn z.1⟩ z.2 = B z.1) =
1 / 2 - (accB T H D n b a₀ a₁ r B - accB T H D n b a₀ a₁ r (fun s => !B s)) / 2` with
`P = tdpPredictor (viewDist T hH D b a₀ a₁) true` and `B = hcBit T h n r`. -/
theorem uprob_predictor_true (h : ∀ i, T.D i → Bool) (hH : PolyTimeComputable H) (D : NUPPT)
    (n : ℕ) (b a₀ a₁ : Bool) (r : T.gen.Coins n) :
    uprob (fun z : T.sample.Coins n × (tdpPredictor (viewDist T hH D b a₀ a₁) true).Coins n =>
        (tdpPredictor (viewDist T hH D b a₀ a₁) true).distinguisherL n
          (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) =
      1 / 2 - (accB T H D n b a₀ a₁ r (hcBit T h n r) -
        accB T H D n b a₀ a₁ r (fun s => !hcBit T h n r s)) / 2 := by
  have h₁ := uprob_tdpPredictor (viewDist T hH D b a₀ a₁) true n (T.index n r)
    (id : T.sample.Coins n → T.sample.Coins n) (hcBit T h n r) List.ofFn
  have h₂ := uprob_signedPredictor_true (hcBit T h n r)
    (fun (yc : T.sample.Coins n × Bool) (ρ : (viewDist T hH D b a₀ a₁).Coins n) =>
      (viewDist T hH D b a₀ a₁).distinguisherL n
        (pairEncode (T.index n r) (pairEncode (List.ofFn yc.1) [yc.2])) ρ)
  rw [acceptProb_viewDist T H hH D n b a₀ a₁ r (hcBit T h n r),
    acceptProb_viewDist T H hH D n b a₀ a₁ r (fun s => !hcBit T h n r s)] at h₂
  exact h₁.trans h₂

/-! ### Bob's side -/

/-- **Bob's side for fixed inputs**: if the two predictors `tdpPredictor D' false/true` for the
bits `(b, a₀, a₁)` of the inputs predict the enhanced bit with probability at most `1/2 + ε_false`
and `1/2 + ε_true` at `n`, then `D`'s advantage between Bob's real and ideal samplers is at most
`|ε_false| + |ε_true|`:
`distAdv (realB π n a b) (idealB S n a b) (D.distinguisherL n) ≤ |εf| + |εt|` under `hf`, `ht`.

**Proof sketch.** With `U± = E_r accB … r (±B)`, the real acceptance is `U+`
(`acceptProb_realB`) and the ideal one `(U+ + U−)/2` (`acceptProb_idealB`), so the advantage is
`|U+ − U−| / 2`. The predictors give `U+ − U− ≤ 2ε_false` and `U− − U+ ≤ 2ε_true`
(`uprob_predictor_false/true`, `uexp_half_add/sub`). -/
theorem distAdv_realB_idealB_le {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    {S : NUPPT} (hS : IsSimB T H S) (D : NUPPT) (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool) (b : Fin (otFunctionality.inB.eval n) → Bool)
    {εf εt : ℝ}
    (hf : uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n ×
        (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) false).Coins n =>
      (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) false).distinguisherL n
        (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) ≤ 1 / 2 + εf)
    (ht : uexp (fun r : T.gen.Coins n => uprob fun z : T.sample.Coins n ×
        (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) true).Coins n =>
      (tdpPredictor (viewDist T hH D (inB1 b 0) (inA2 a 0) (inA2 a 1)) true).distinguisherL n
        (pairEncode (T.index n r) (List.ofFn z.1)) z.2 = hcBit T h n r z.1) ≤ 1 / 2 + εt) :
    distAdv (otFunctionality.realB π n a b) (otFunctionality.idealB S n a b)
      (D.distinguisherL n) ≤ |εf| + |εt| := by
  simp only [uprob_predictor_false T H h hH D n, uprob_predictor_true T H h hH D n] at hf ht
  rw [uexp_half_add] at hf
  rw [uexp_half_sub] at ht
  rw [distAdv_def, acceptProb_realB T H henc hπ houtP, acceptProb_idealB T H (h := h) hS,
    show (fun r => (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) / 2) =
      fun r => (1 / 2 : ℝ) * (accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r) +
        accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (fun s => !hcBit T h n r s)) from
      funext fun r => by ring,
    HardcoreBit.uexp_const_mul, HardcoreBit.uexp_add]
  generalize uexp (fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r (hcBit T h n r)) = U₁
    at hf ht ⊢
  generalize uexp (fun r => accB T H D n (inB1 b 0) (inA2 a 0) (inA2 a 1) r
    (fun s => !hcBit T h n r s)) = U₂ at hf ht ⊢
  have h₁ := le_abs_self εf
  have h₂ := le_abs_self εt
  have h₃ := abs_nonneg εf
  have h₄ := abs_nonneg εt
  rw [abs_le]
  constructor <;> linarith

/-- **Bob's side of Proposition 161.5** [PS10]: under the enhanced hard-core hypothesis (stated
explicitly, `hEHC`), for every distinguisher `D` there is a negligible `ε ≥ 0` bounding `D`'s
advantage between Bob's real and ideal samplers for all `n` and all inputs.

**Proof sketch.** `hEHC` gives a negligible `ε_{t, fl}` for each of the sixteen predictors
`tdpPredictor (viewDist D t) fl`, `t = (b, a₀, a₁)`, `fl ∈ {0, 1}`. Take
`ε(n) = Σ_t Σ_fl |ε_{t, fl}(n)|` (negligible by `negligible_finset_sum`): for the inputs' bits
`t`, `distAdv_realB_idealB_le` bounds the advantage by `|ε_{t, 0}(n)| + |ε_{t, 1}(n)| ≤ ε(n)`. -/
theorem exists_negligible_bob {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    {S : NUPPT} (hS : IsSimB T H S)
    (hEHC : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      uexp (fun r : T.gen.Coins n =>
        uprob fun z : T.sample.Coins n × A.Coins n =>
          A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
            h (T.index n r) ((T.perm (T.index n r)).symm
              ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
        ≤ 1 / 2 + ε n)
    (D : NUPPT) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ (∀ n, 0 ≤ ε n) ∧
      ∀ n (a : Fin (otFunctionality.inA.eval n) → Bool)
        (b : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realB π n a b) (otFunctionality.idealB S n a b)
          (D.distinguisherL n) ≤ ε n := by
  choose ε hε hb using fun (t : Bool × Bool × Bool) (fl : Bool) =>
    hEHC (tdpPredictor (viewDist T hH D t.1 t.2.1 t.2.2) fl)
  refine ⟨fun n => ∑ t : Bool × Bool × Bool, ∑ fl : Bool, |ε t fl n|,
    negligible_finset_sum _ fun t _ => negligible_finset_sum _ fun fl _ =>
      (hε t fl).mono ⟨0, fun n _ => (abs_abs _).le⟩,
    fun n => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun n a b => ?_⟩
  refine (distAdv_realB_idealB_le T H hH henc hπ houtP hS D n a b
    (hb (inB1 b 0, inA2 a 0, inA2 a 1) false n) (hb (inB1 b 0, inA2 a 0, inA2 a 1) true n)).trans ?_
  have hsum : ∑ fl : Bool, |ε (inB1 b 0, inA2 a 0, inA2 a 1) fl n| =
      |ε (inB1 b 0, inA2 a 0, inA2 a 1) false n| + |ε (inB1 b 0, inA2 a 0, inA2 a 1) true n| := by
    rw [Fintype.sum_bool, add_comm]
  rw [← hsum]
  exact Finset.single_le_sum (f := fun t => ∑ fl : Bool, |ε t fl n|)
    (fun t _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ _)

/-- **Proposition 161.5 with its simulators** [PS10], for every protocol of the shape of
Protocol 160.4 (with Bob's output `[a_b]` and Alice's `[]`) and every pair of machines of the
shapes of `S_A` and `S_B`: for a collection of one-way trapdoor permutations with an enhanced
hard-core predicate (`hEHC`, explicit) evaluated on encodings by `H`, each distinguisher has
a negligible `ε` bounding both advantages for all `n` and all inputs:
`∀ D, ∃ ε, Negligible ε ∧ ∀ n x y, distAdv (realA π n x y) (idealA SA n x y) (D.distinguisherL n)
≤ ε n ∧ distAdv (realB π n x y) (idealB SB n x y) (D.distinguisherL n) ≤ ε n`.

**Proof sketch.** `T.OneWay` gives a negligible `δ` with `SampleClose δ`. Alice's side is at
most `2δ(n)` (`distAdv_realA_idealA_le`), Bob's at most a negligible `ε_B(n) ≥ 0`
(`exists_negligible_bob`). Take `ε(n) = 2|δ(n)| + ε_B(n)`. -/
theorem simulators_of_isOT {h : ∀ i, T.D i → Bool} (hH : PolyTimeComputable H)
    (henc : ∀ i (x : T.D i), H (pairEncode i (T.encD i x)) = [h i x]) {π : Protocol}
    (hπ : IsOT T H π)
    (houtV : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outV π.P x (List.ofFn a) (List.ofFn b) r = [a (if b 0 then 1 else 0)])
    (houtP : ∀ x (a : Fin 2 → Bool) (b : Fin 1 → Bool) (r : π.ExecCoins π.P x),
      π.outP x (List.ofFn a) (List.ofFn b) r = [])
    {SA SB : NUPPT} (hSA : IsSimA T SA) (hSB : IsSimB T H SB) (hT : T.OneWay)
    (hEHC : ∀ A : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      uexp (fun r : T.gen.Coins n =>
        uprob fun z : T.sample.Coins n × A.Coins n =>
          A.distinguisherL n (pairEncode (T.index n r) (List.ofFn z.1)) z.2 =
            h (T.index n r) ((T.perm (T.index n r)).symm
              ((T.decD (T.index n r) (T.sample.runAt n (T.index n r) z.1)).getD default)))
        ≤ 1 / 2 + ε n) :
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n (x : Fin (otFunctionality.inA.eval n) → Bool)
        (y : Fin (otFunctionality.inB.eval n) → Bool),
        distAdv (otFunctionality.realA π n x y) (otFunctionality.idealA SA n x y)
            (D.distinguisherL n) ≤ ε n ∧
          distAdv (otFunctionality.realB π n x y) (otFunctionality.idealB SB n x y)
            (D.distinguisherL n) ≤ ε n := by
  obtain ⟨δ, hδ, hδS⟩ := ((TrapdoorCollection.oneWay_iff T).1 hT).sampleClose
  intro D
  obtain ⟨εB, hεB, h0, hB⟩ := exists_negligible_bob T H hH henc hπ houtP hSB hEHC D
  refine ⟨fun n => 2 * |δ n| + εB n,
    ((hδ.mono ⟨0, fun n _ => (abs_abs _).le⟩).const_mul 2).add hεB, fun n x y => ⟨?_, ?_⟩⟩
  · have hA := distAdv_realA_idealA_le T H hπ houtV hSA hδS D n x y
    have := le_abs_self (δ n)
    have := h0 n
    linarith
  · have := hB n x y
    have := abs_nonneg (δ n)
    linarith

end TCSlib.Cryptography.SecureComputation.OT
