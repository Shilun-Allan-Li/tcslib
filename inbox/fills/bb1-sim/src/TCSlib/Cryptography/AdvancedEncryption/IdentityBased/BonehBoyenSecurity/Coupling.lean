/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Step M of BB1's simulation: the real game against the simulator, call by call

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). After `h` is drawn at the first `Init`
(`BB1Sim.bb1RealLazy`) and the challenge coin `c` at the first valid `Challenge`
(`BB1Sim.bb1SimLazy`), the real game and the simulator answer alike call by call, on states
related by design r1 §3.1's relation `RelM`: the same recorded challenge, the same committed
identity `ID*`, and `h = X^{−ID*} g^{α_1}` [BB04, proof of Theorem 4.1, *Setup*]. The real
`KeyGen` exponent `r̃` and the simulated one `r` correspond by `r = r̃ + b/(ID − ID*)`
[BB04, proof of Theorem 4.1, *Phase 1*], which needs `ID ≠ ID*` in `Z_p`: the generator's coins
must give `2^ℓ ≤ p`. The challenge is `Encrypt` with `s = c`
[BB04, proof of Theorem 4.1, *Challenge*].

## Main definitions

* `BB1Sim.RelM` — the relation of step M.

## Main results

* `BB1Sim.exists_equiv_mul_pow`, `BB1Sim.natCast_bitsToNat_injective`, `BB1Sim.key_eq`,
  `BB1Sim.F_target_eq`, `BB1Sim.pair_pow_val_eq` — the group algebra of the coupling.
* `BB1Sim.stepM_init_none`, …, `BB1Sim.stepM_challenge_fresh` — step M, call by call.
* `BB1Sim.stepM_call` — the per-call hypothesis of `ProbComp.expect_simulate_rel`.
* `BB1Sim.expect_simulate_bb1RealLazy` — step M: on good coins, the real game with `h` drawn at
  `Init` simulates like the lazy simulator on `Y = g^{b'}` with `c` drawn at the challenge.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
  Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

/-! ### The group algebra of the coupling -/

section Algebra

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **`h ↦ α_1` along `h = X^{−z} g^{α_1}`** [BB04, proof of Theorem 4.1, *Setup*]: for `g ≠ 1`
and every `X`, there are bijections `e z : G ≃ Z_p`, one for each `z ∈ Z_p`, with
`h = X^{(−z).val} · g^{(e z h).val}` for every `h`. -/
theorem exists_equiv_mul_pow {g : B.G} (hg : g ≠ 1) (X : B.G) :
    ∃ e : ZMod B.order → B.G ≃ ZMod B.order,
      ∀ z h, h = X ^ (-z).val * g ^ (e z h).val := by
  let E : ZMod B.order ≃ B.G := Equiv.ofBijective _ (B.pow_val_bijective_of_ne_one hg)
  refine ⟨fun z => (Equiv.mulLeft (X ^ (-z).val)⁻¹).trans E.symm, fun z h => ?_⟩
  have hE : g ^ (E.symm ((X ^ (-z).val)⁻¹ * h)).val = (X ^ (-z).val)⁻¹ * h :=
    E.apply_symm_apply _
  show h = X ^ (-z).val * g ^ (E.symm ((X ^ (-z).val)⁻¹ * h)).val
  rw [hE, mul_inv_cancel_left]

/-- **Distinct `n`-bit identities are distinct in `Z_p` when `2^n ≤ p`**: reading `n`-bit strings
as numbers modulo `p` is injective, `fun u => (bitsToNat u : ZMod p)`. Glue for
[BB04, §4.4]'s condition on the identity length. -/
theorem natCast_bitsToNat_injective {n p : ℕ} (hp : 2 ^ n ≤ p) :
    Function.Injective fun u : Fin n → Bool => (bitsToNat u : ZMod p) := fun u v huv =>
  bitsToNat_injective (CharP.natCast_injOn_Iio (ZMod p) p (lt_of_lt_of_le (bitsToNat_lt u) hp)
    (lt_of_lt_of_le (bitsToNat_lt v) hp) huv)

/-- **The simulated key is a real key** [BB04, proof of Theorem 4.1, *Phase 1*, "let
`r̃_j = r_j − b/(I_j − I^*_j)`"]: for `X = g^α`, `Y = g^{b'}`, `z ≠ z'` and
`F(z) = X^z · (X^{−z'} g^{α_1})`, the real key `(Y^α F(z)^r, g^r)` with exponent `r` is the
simulated key `(Y^{−α_1/(z − z')} F(z)^{r'}, Y^{−1/(z − z')} g^{r'})` with exponent
`r' = r + b'/(z − z')`. -/
theorem key_eq (g : B.G) (α b' z z' a₁ r : ZMod B.order) (hz : z ≠ z') :
    (g ^ b'.val) ^ α.val *
        ((g ^ α.val) ^ z.val * ((g ^ α.val) ^ (-z').val * g ^ a₁.val)) ^ r.val =
      (g ^ b'.val) ^ (-a₁ / (z - z')).val *
        ((g ^ α.val) ^ z.val * ((g ^ α.val) ^ (-z').val * g ^ a₁.val)) ^ (r + b' / (z - z')).val ∧
    g ^ r.val = (g ^ b'.val) ^ (-1 / (z - z')).val * g ^ (r + b' / (z - z')).val := by
  have hz' : z - z' ≠ 0 := sub_ne_zero.2 hz
  have hpow : ∀ a c : ZMod B.order, (g ^ a.val) ^ c.val = g ^ (a * c).val := fun a c => by
    rw [B.pow_val_mul, pow_mul]
  have hmul : ∀ a c : ZMod B.order, g ^ a.val * g ^ c.val = g ^ (a + c).val := fun a c =>
    (B.pow_val_add g a c).symm
  simp only [hpow, hmul]
  constructor <;> congr 2 <;> field_simp <;> ring

/-- **`F(ID*) = g^{α_1}`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
`F_i(I^*_i) = g^{α_i}`"]: for `h = X^{−z} g^{α_1}`, `X^z · h = g^{α_1}`. -/
theorem F_target_eq (g X : B.G) (z a₁ : ZMod B.order) :
    X ^ z.val * (X ^ (-z).val * g ^ a₁.val) = g ^ a₁.val := by
  rw [B.pow_val_neg, mul_inv_cancel_left]

/-- **`e(g^α, g^{b'})^s = e(g, g)^{α b' s}`** [BB04, proof of Theorem 4.1, *Challenge*, "if
`T = e(g, g)^{abc} = e(g_1, g_2)^c`"]: `B.pair (g^α) (g^{b'}) ^ s.val =
B.pair g g ^ (α · b' · s).val`. -/
theorem pair_pow_val_eq (g : B.G) (α b' s : ZMod B.order) :
    B.pair (g ^ α.val) (g ^ b'.val) ^ s.val = B.pair g g ^ (α * b' * s).val := by
  rw [B.pow_val_mul_GT, pow_mul, B.pow_val_mul_GT, B.bilinear_pow]

end Algebra

/-! ### The relation of step M -/

section Rel

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)

/-- **Design r1 §3.1's relation `R`** [BB04, proof of Theorem 4.1, *Setup*]: the real state `u`
(with `h`) and the simulator's state `v` (with `α_1`) record the same challenge and the same
committed identity `ID*`, and `h = X^{−ID*} g^{α_1}`. -/
def RelM (g X : (G.group κ d).G) (u : BB1RealState G ℓ κ d) (v : BB1SimState G ℓ κ d) : Prop :=
  u.2 = v.2 ∧ Option.Rel (fun p q => p.1 = q.1 ∧
    p.2 = X ^ (-BB1.idToZ (G.group κ d) p.1).val * g ^ q.2.val) u.1 v.1

/-- `RelM … g X u v` holds iff `u.2 = v.2` and `u.1`, `v.1` are both `none`, or `some (t, h)` and
`some (t, α_1)` with `h = X^{(−idToZ t).val} · g^{α_1.val}`. -/
theorem relM_iff (g X : (G.group κ d).G) (u : BB1RealState G ℓ κ d) (v : BB1SimState G ℓ κ d) :
    RelM G ℓ κ d g X u v ↔ u.2 = v.2 ∧ Option.Rel (fun p q => p.1 = q.1 ∧
      p.2 = X ^ (-BB1.idToZ (G.group κ d) p.1).val * g ^ q.2.val) u.1 v.1 := Iff.rfl

end Rel

/-! ### Step M, call by call

The real side is `bb1RealLazy` on parameters `o h` that the game reads as `(g, g^α, g^{b'}, h)`
(`RealReads`); the simulator is `bb1SimLazy` on `X = g^α`, `Y = g^{b'}`, with the challenge coin
`c ∈ Z_p` drawn at the first valid `Challenge`. Deterministic calls answer alike and keep the
states; sampling calls give the premise of `ProbComp.expect_sample_rel` along their bijection. -/

section StepM

variable (G : BilinearGen) (ℓ : PolyExpr) (b : Bool) (κ : ℕ) (d : List Bool)
  (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)
  (g : (G.group κ d).G) (α b' : ZMod (G.group κ d).order)

variable {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)

/-- **Step M, `Init` before a commitment** [BB04, proof of Theorem 4.1, *Setup*] (sampling): the
real call draws `h ∈ G`, the simulator draws `α_1 ∈ Z_p`; along the bijection `e ID` with
`h = X^{−z} g^{e z h}` (`exists_equiv_mul_pow`) at `z = ID`, they answer alike and reach related
states: `(f₀ h).1 = (f₁ (e ID h)).1` and `RelM (f₀ h).2 (f₁ (e ID h)).2`.

**Proof sketch.** The real call is read by `bb1RealLazy_zero_none`, `sidImpl_zero_onSpec` and
`sidImpl_init_none` (a uniform `h`, the parameters `o h`, the identity recorded with `h`); the
simulator's by `bb1SimLazy_zero`, `oracleImpl_zero_onSpec` and `bb1SimInit_none` (a uniform
`α_1`). At `α_1 = e ID h` the parameter words agree (`RealReads.encPP`, `ofFn_bb1Scheme_encPP`,
`bb1SimParams_eq`, `h = X^{−ID} g^{e ID h}`), and that equation is `RelM` of the new states. -/
theorem stepM_init_none (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (e : ZMod (G.group κ d).order → (G.group κ d).G ≃ ZMod (G.group κ d).order)
    (he : ∀ z h, h = (g ^ α.val) ^ (-z).val * g ^ (e z h).val) :
    ∃ (f₀ : (G.group κ d).G → ((bb1Scheme G ℓ).sidSpec κ).rng 0 × BB1RealState G ℓ κ d)
      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 0 × BB1SimState G ℓ κ d),
      bb1RealLazy G ℓ b κ d o 0 x (none, c) =
        (ProbComp.sample (G.group κ d).G).bind (fun h => .pure (f₀ h)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 0 x (none, c) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun α₁ => .pure (f₁ α₁)) ∧
      ∀ h, (f₀ h).1 = (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).1 ∧
        RelM G ℓ κ d g (g ^ α.val) (f₀ h).2
          (f₁ (e (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h)).2 := by
  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
  case h0 =>
    rw [bb1RealLazy_zero_none]
    refine congrArg _ (funext fun h => ?_)
    rw [IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_none, OracleComp.pure_bind,
      OracleComp.pure_bind]
  case h1 =>
    rw [bb1SimLazy_zero, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec, bb1SimInit_none,
      OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  case hf =>
    intro h
    have hz := he (BB1.idToZ (G.group κ d) (cast (sidSpec_dom_zero _ κ) x)) h
    refine ⟨?_, ⟨rfl, .some ⟨rfl, ?_⟩⟩⟩
    · rw [(ho h).encPP, List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ d _), bb1SimParams_eq,
        ← hz]
    · dsimp only
      exact hz

/-- **Step M, `Init` after a commitment** [BB04, proof of Theorem 4.1, *Setup*] (deterministic):
for `h = X^{−ID*} g^{α_1}`, both calls answer the same parameters `(g, X, Y, h)` and keep their
states: `bb1RealLazy … 0 x (some (t, h), c) = pure (a, (some (t, h), c))` and
`bb1SimLazy … 0 x (some (t, α_1), c) = pure (a, (some (t, α_1), c))`.

**Proof sketch.** The real call is `sidImpl`'s `Init` on a committed state (`bb1RealLazy_some`,
`sidImpl_zero_onSpec`, `sidImpl_init_some`); the simulator's is `bb1SimInit_some`
(`bb1SimLazy_zero`, `bb1SimImpl_eq`, `oracleImpl_zero_onSpec`). Both answer the encoded parameters,
equal by `RealReads.encPP`, `ofFn_bb1Scheme_encPP`, `bb1SimParams_eq` and `h = X^{−ID*} g^{α_1}`. -/
theorem stepM_init_some (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val) :
    ∃ a, bb1RealLazy G ℓ b κ d o 0 x (some (t, h), c) = .pure (a, (some (t, h), c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 0 x (some (t, α₁), c) =
        .pure (a, (some (t, α₁), c)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_some,
      OracleComp.pure_bind, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_zero, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec, bb1SimInit_some,
      OracleComp.pure_bind, (ho h).encPP, List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ d _),
      bb1SimParams_eq, ← hh]

/-- **Step M, `KeyGen` before `Init`** (deterministic): both calls answer `⊥` and keep their
states: `bb1RealLazy … 1 x (none, c) = pure (a, (none, c))` and
`bb1SimLazy … 1 x (none, c) = pure (a, (none, c))`. Glue for the game's `KeyGen`. -/
theorem stepM_keyGen_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    ∃ a, bb1RealLazy G ℓ b κ d o 1 x (none, c) = .pure (a, (none, c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (none, c) =
        .pure (a, (none, c)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_none_of_ne _ _ _ _ _ _ 1 (by decide), IBEScheme.sidImpl_one_onQuery,
      IBEScheme.sidImpl_keyGen_none, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_none,
      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]

/-- **Step M, `KeyGen` for `ID*`** (deterministic): both calls answer `⊥` and keep their states:
for `x` read as `t`, `bb1RealLazy … 1 x (some (t, h), c) = pure (a, (some (t, h), c))` and
`bb1SimLazy … 1 x (some (t, α_1), c) = pure (a, (some (t, α_1), c))`. Glue for the game's
`KeyGen`.

**Proof sketch.** The real call is `sidImpl_keyGen_target` (`bb1RealLazy_some`,
`sidImpl_one_onQuery`), the simulator's `bb1SimKeyQ_target` (`bb1SimLazy_one`, `bb1SimImpl_eq`,
`oracleImpl_one_onSpec`); both `⊥` words agree by `zeroBits_eq_cast` and `outLens_one`. -/
theorem stepM_keyGen_target (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (α₁ : ZMod (G.group κ d).order) (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (ht : cast (sidSpec_dom_one _ κ) x = t) :
    ∃ a, bb1RealLazy G ℓ b κ d o 1 x (some (t, h), c) = .pure (a, (some (t, h), c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (some (t, α₁), c) =
        .pure (a, (some (t, α₁), c)) := by
  subst ht
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_one_onQuery, IBEScheme.sidImpl_keyGen_target,
      OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_target,
      OracleComp.pure_bind, zeroBits_eq_cast (IBEScheme.outLens_one _ κ) (sidSpec_rng_one _ κ).symm]

/-- **Step M, `KeyGen` for `ID ≠ ID*`** [BB04, proof of Theorem 4.1, *Phase 1*, "let
`r̃_j = r_j − b/(I_j − I^*_j)`"] (sampling): for `h = X^{−ID*} g^{α_1}` and good coins
`2^{ℓ(κ)} ≤ p`, the real key with exponent `r̃` is the simulated key with exponent
`r̃ + b'/(ID − ID*)`: `(f₀ r̃).1 = (f₁ (r̃ + b'/(ID − ID*))).1`, and the states are kept.

**Proof sketch.** The real call is read by `sidImpl_keyGen_ne_onSpec` and `RealReads.keyGen` (a
uniform `r̃` and the key word), the simulator's by `oracleImpl_one_onSpec` and `bb1SimKeyQ_ne` (a
uniform `r`). `ID ≠ ID*` in `Z_p` by `natCast_bitsToNat_injective` (`BB1.idToZ_eq`). At
`r = r̃ + b'/(ID − ID*)` the key words agree: `ofFn_bb1Scheme_encSK`, `bb1SimKey_eq`, `BB1.F_eq`,
`bb1SimParams_eq`, `h = X^{−ID*} g^{α_1}` and `key_eq`. The states are unchanged. -/
theorem stepM_keyGen_ne (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (α₁ : ZMod (G.group κ d).order) (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)
    (ht : cast (sidSpec_dom_one _ κ) x ≠ t) :
    ∃ (f₀ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 1 × BB1RealState G ℓ κ d)
      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 1 × BB1SimState G ℓ κ d),
      bb1RealLazy G ℓ b κ d o 1 x (some (t, h), c) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun r => .pure (f₀ r)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 1 x (some (t, α₁), c) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun r => .pure (f₁ r)) ∧
      ∀ r, (f₀ r).1 = (f₁ (Equiv.addRight (b' / (BB1.idToZ (G.group κ d)
          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).1 ∧
        RelM G ℓ κ d g (g ^ α.val) (f₀ r).2 (f₁ (Equiv.addRight (b' / (BB1.idToZ (G.group κ d)
          (cast (sidSpec_dom_one _ κ) x) - BB1.idToZ (G.group κ d) t)) r)).2 := by
  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_keyGen_ne_onSpec _ _ _ _ _ x t c ht,
      OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind, Option.map_some]
    rw [(ho h).keyGen _ fun w => .pure (cast (sidSpec_rng_one _ κ).symm
      (FixedLengthScheme.decAnswer (some w)), (some (t, h), c))]
  case h1 =>
    rw [bb1SimLazy_one, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec, bb1SimKeyQ_ne (h := ht),
      OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    rfl
  case hf =>
    intro r
    refine ⟨?_, ⟨rfl, .some ⟨rfl, hh⟩⟩⟩
    have hz : BB1.idToZ (G.group κ d) (cast (sidSpec_dom_one _ κ) x) ≠
        BB1.idToZ (G.group κ d) t := by
      rw [BB1.idToZ_eq, BB1.idToZ_eq]
      exact fun h' => ht (natCast_bitsToNat_injective hp h')
    obtain ⟨h0, h1⟩ := key_eq (G.group κ d) g α b' _ _ α₁ r hz
    rw [Equiv.coe_addRight, List.ofFn_injective (ofFn_bb1Scheme_encSK G ℓ κ d _), bb1SimKey_eq,
      BB1.F_eq, BB1.F_eq, bb1SimParams_eq, hh]
    dsimp only
    rw [h0, h1]

/-- **Step M, `Challenge` before `Init`** (deterministic): both calls answer `⊥` and keep their
states: `bb1RealLazy … 2 x (none, c) = pure (a, (none, c))` and
`bb1SimLazy … 2 x (none, c) = pure (a, (none, c))`. Glue for the game's `Challenge`. -/
theorem stepM_challenge_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (none, c) = .pure (a, (none, c)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (none, c) =
        .pure (a, (none, c)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_none_of_ne _ _ _ _ _ _ 2 (by decide), IBEScheme.sidImpl_two_onQuery,
      IBEScheme.sidImpl_challenge_none, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (none, c) fun h' => Bool.false_ne_true h'.1,
      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_none, OracleComp.pure_bind,
      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]

/-- **Step M, `Challenge` after a recorded challenge** (deterministic): both calls repeat the
recorded challenge `w` and keep their states: `bb1RealLazy … 2 x (some (t, h), some w) =
pure (a, (some (t, h), some w))` and `bb1SimLazy … 2 x (some (t, α_1), some w) =
pure (a, (some (t, α_1), some w))`. Glue for the game's `Challenge`.

**Proof sketch.** The real call is `sidImpl_challenge_repeat` (`bb1RealLazy_some`,
`sidImpl_two_onSpec`), the simulator's `bb1SimChal_repeat` (`bb1SimLazy_two_of_not`, since a
challenge is recorded; `bb1SimImpl_eq`, `oracleImpl_two_onSpec`); both answer `w`. -/
theorem stepM_challenge_repeat (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (α₁ : ZMod (G.group κ d).order) (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) :
    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (some (t, h), some w) = .pure (a, (some (t, h), some w)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (some (t, α₁), some w) =
        .pure (a, (some (t, α₁), some w)) := by
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_two_onSpec, IBEScheme.sidImpl_challenge_repeat,
      OracleComp.pure_bind, OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (some (t, α₁), some w)
        fun h' => Option.some_ne_none w h'.2.1,
      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_repeat, OracleComp.pure_bind]

/-- **Step M, the first invalid `Challenge`** (deterministic): when a message of the query is not
an encoding of `G_T`, both calls answer `⊥` and keep their states:
`bb1RealLazy … 2 x (some (t, h), none) = pure (a, (some (t, h), none))` and
`bb1SimLazy … 2 x (some (t, α_1), none) = pure (a, (some (t, α_1), none))`; both message spaces
are the encodings of `G_T` (`RealReads.msgSpace`, `bb1Scheme_msgSpace_iff`). Glue for the
game's `Challenge`.

**Proof sketch.** The real call is read by `bb1RealLazy_some`, `sidImpl_two_onQuery` and
`sidImpl_challenge_invalid` (invalidity through `RealReads.msgSpace`); the simulator's by
`bb1SimLazy_two_of_not`, `oracleImpl_two_onSpec` and `bb1SimChal_invalid` (invalidity through
`bb1Scheme_msgSpace_iff`). Both answer the `⊥` word (`zeroBits_eq_cast`). -/
theorem stepM_challenge_invalid (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
    (hv : ¬ ((∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
      ∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
    ∃ a, bb1RealLazy G ℓ b κ d o 2 x (some (t, h), none) = .pure (a, (some (t, h), none)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val) zt 2 x (some (t, α₁), none) =
        .pure (a, (some (t, α₁), none)) := by
  have hv' : ¬ ((bb1Scheme G ℓ).MsgSpace κ (o h).1
        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1 ∧
      (bb1Scheme G ℓ).MsgSpace κ (o h).1
        (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) := fun hm =>
    hv ⟨((ho h).msgSpace _).1 hm.1, ((ho h).msgSpace _).1 hm.2⟩
  refine ⟨?a, ?h0, ?h1⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_two_onQuery,
      IBEScheme.sidImpl_challenge_invalid _ _ _ _ _ _ _ hv', OracleComp.pure_bind]
    rfl
  case h1 =>
    rw [bb1SimLazy_two_of_not G ℓ b κ d g _ _ zt x (some (t, α₁), none) fun h' => hv h'.2.2,
      bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_invalid, OracleComp.pure_bind,
      zeroBits_eq_cast (IBEScheme.outLens_two _ κ) (sidSpec_rng_two _ κ).symm]
    exact fun hm => hv ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm.1,
      (bb1Scheme_msgSpace_iff G ℓ κ d _ _).1 hm.2⟩

/-- **Step M, the first valid `Challenge`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
`F_i(I^*_i) = g^{α_i}`"] (sampling, along the identity of `Z_p`): for `h = X^{−ID*} g^{α_1}`,
the real encryption with exponent `s` is the simulated challenge on the coins
`(g^s, e(g, g)^{α b' s})`: `(f₀ s).1 = (f₁ s).1`, and both record that challenge.

**Proof sketch.** The real call is read by `sidImpl_challenge_fresh_onSpec` (validity through
`RealReads.msgSpace`) and `RealReads.enc` (a uniform `s` and the ciphertext word); the
simulator's by `bb1SimLazy_two_fresh` (a uniform `c`), `oracleImpl_two_onSpec` and
`bb1SimChal_fresh` (validity through `bb1Scheme_msgSpace_iff`). At `c = s` the words agree
(`ofFn_bb1SimCt`, `pair_pow_val_eq`, commutativity of `G_T`, `BB1.F_eq`, `F_target_eq`,
`pow_right_comm`), and both record that word. -/
theorem stepM_challenge_fresh (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h))
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool)
    (h : (G.group κ d).G) (α₁ : ZMod (G.group κ d).order)
    (hh : h = (g ^ α.val) ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)
    (hv : (∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
      ∃ u, List.ofFn ((G.group κ d).encT u) =
        List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2) :
    ∃ (f₀ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 2 × BB1RealState G ℓ κ d)
      (f₁ : ZMod (G.group κ d).order → ((bb1Scheme G ℓ).sidSpec κ).rng 2 × BB1SimState G ℓ κ d),
      bb1RealLazy G ℓ b κ d o 2 x (some (t, h), none) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun s => .pure (f₀ s)) ∧
      bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
          (fun c : ZMod (G.group κ d).order =>
            (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) 2 x (some (t, α₁), none) =
        (ProbComp.sample (ZMod (G.group κ d).order)).bind (fun c => .pure (f₁ c)) ∧
      ∀ s, (f₀ s).1 = (f₁ (Equiv.refl _ s)).1 ∧
        RelM G ℓ κ d g (g ^ α.val) (f₀ s).2 (f₁ (Equiv.refl _ s)).2 := by
  refine ⟨?f₀, ?f₁, ?h0, ?h1, ?hf⟩
  case h0 =>
    rw [bb1RealLazy_some, IBEScheme.sidImpl_challenge_fresh_onSpec _ _ _ _ _ x t
      ⟨((ho h).msgSpace _).2 hv.1, ((ho h).msgSpace _).2 hv.2⟩, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind, Option.map_some]
    rw [(ho h).enc t _ fun w => .pure (cast (sidSpec_rng_two _ κ).symm w, (some (t, h), some w))]
  case h1 =>
    rw [bb1SimLazy_two_fresh G ℓ b κ d g _ _ _ x _ ⟨rfl, rfl, hv⟩]
    refine congrArg _ (funext fun c => ?_)
    rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh, OracleComp.pure_bind]
    exact ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1, (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩
  case hf =>
    intro s
    rw [Equiv.refl_apply]
    refine ⟨?_, ⟨?_, .some ⟨rfl, hh⟩⟩⟩ <;>
    · rw [List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _), pair_pow_val_eq,
        mul_comm ((G.group κ d).pair g g ^ (α * b' * s).val), BB1.F_eq]
      dsimp only
      rw [hh, F_target_eq, pow_right_comm]

/-- **Step M, the per-call hypothesis of `ProbComp.expect_simulate_rel`** [BB04, proof of
Theorem 4.1]: for `g ≠ 1`, good coins `2^{ℓ(κ)} ≤ p`, and parameters `o h` read as
`(g, g^α, g^{b'}, h)`, from states related by `RelM`, a call of `bb1RealLazy … o` and of
`bb1SimLazy` on `X = g^α`, `Y = g^{b'}` and `zt c = (g^c, e(g, g)^{α b' c})` give the same
expectation to any `g₀`, `g₁` that agree at equal answers and related states.

**Proof sketch.** By cases on the oracle and the states, with the rows `stepM_*`: deterministic
rows answer alike and keep the related states (`expect_pure`); sampling rows meet the premise of
`ProbComp.expect_sample_rel` along `e ID` (`Init`, `exists_equiv_mul_pow`),
`r ↦ r + b'/(ID − ID*)` (`KeyGen`, `key_eq`, `natCast_bitsToNat_injective`) and the identity
(`Challenge`, `F_target_eq`, `pair_pow_val_eq`). -/
theorem stepM_call (hg : g ≠ 1) (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) (i : Fin 3)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom i) (u : BB1RealState G ℓ κ d)
    (v : BB1SimState G ℓ κ d) (huv : RelM G ℓ κ d g (g ^ α.val) u v)
    (g₀ : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1RealState G ℓ κ d → ℝ)
    (g₁ : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ)
    (hg₀₁ : ∀ y u' v', RelM G ℓ κ d g (g ^ α.val) u' v' → g₀ (y, u') = g₁ (y, v')) :
    ProbComp.expect (bb1RealLazy G ℓ b κ d o i x u) g₀ =
      ProbComp.expect (bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
        (fun c : ZMod (G.group κ d).order =>
          (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) i x v) g₁ := by
  generalize hzt : (fun c : ZMod (G.group κ d).order =>
    (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val)) = zt
  obtain ⟨e, he⟩ := exists_equiv_mul_pow (G.group κ d) hg (g ^ α.val)
  obtain ⟨u₁, uc⟩ := u
  obtain ⟨v₁, vc⟩ := v
  obtain ⟨hc, hR⟩ := id huv
  dsimp only at hc
  subst hc
  match i, x, g₀, g₁, hg₀₁ with
  | 0, x, g₀, g₁, hg₀₁ =>
    cases hR with
    | none =>
      obtain ⟨f₀, f₁, h0, h1, hf⟩ := stepM_init_none G ℓ b κ d o g α b' zt ho x uc e he
      rw [h0, h1]
      exact ProbComp.expect_sample_rel _ (e _) f₀ f₁ hf g₀ g₁ hg₀₁
    | @some p q hpq =>
      obtain ⟨t, h⟩ := p
      obtain ⟨t', α₁⟩ := q
      obtain ⟨ht, hh⟩ := hpq
      dsimp only at ht hh
      subst t'
      obtain ⟨a, h0, h1⟩ := stepM_init_some G ℓ b κ d o g α b' zt ho x t h α₁ uc hh
      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
      exact hg₀₁ _ _ _ huv
  | 1, x, g₀, g₁, hg₀₁ =>
    cases hR with
    | none =>
      obtain ⟨a, h0, h1⟩ := stepM_keyGen_none G ℓ b κ d o g α b' zt x uc
      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
      exact hg₀₁ _ _ _ huv
    | @some p q hpq =>
      obtain ⟨t, h⟩ := p
      obtain ⟨t', α₁⟩ := q
      obtain ⟨ht, hh⟩ := hpq
      dsimp only at ht hh
      subst t'
      by_cases hx : cast (sidSpec_dom_one _ κ) x = t
      · obtain ⟨a, h0, h1⟩ := stepM_keyGen_target G ℓ b κ d o g α b' zt x t h α₁ uc hx
        rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
        exact hg₀₁ _ _ _ huv
      · obtain ⟨f₀, f₁, h0, h1, hf⟩ :=
          stepM_keyGen_ne G ℓ b κ d o g α b' zt hp ho x t h α₁ uc hh hx
        rw [h0, h1]
        exact ProbComp.expect_sample_rel _ (Equiv.addRight _) f₀ f₁ hf g₀ g₁ hg₀₁
  | 2, x, g₀, g₁, hg₀₁ =>
    cases hR with
    | none =>
      obtain ⟨a, h0, h1⟩ := stepM_challenge_none G ℓ b κ d o g α b' zt x uc
      rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
      exact hg₀₁ _ _ _ huv
    | @some p q hpq =>
      obtain ⟨t, h⟩ := p
      obtain ⟨t', α₁⟩ := q
      obtain ⟨ht, hh⟩ := hpq
      dsimp only at ht hh
      subst t'
      rcases uc with _ | w
      · by_cases hv : (∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2
        · subst hzt
          obtain ⟨f₀, f₁, h0, h1, hf⟩ :=
            stepM_challenge_fresh G ℓ b κ d o g α b' ho x t h α₁ hh hv
          rw [h0, h1]
          exact ProbComp.expect_sample_rel _ (Equiv.refl _) f₀ f₁ hf g₀ g₁ hg₀₁
        · obtain ⟨a, h0, h1⟩ := stepM_challenge_invalid G ℓ b κ d o g α b' zt ho x t h α₁ hv
          rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
          exact hg₀₁ _ _ _ huv
      · obtain ⟨a, h0, h1⟩ := stepM_challenge_repeat G ℓ b κ d o g α b' zt x t h α₁ w
        rw [h0, h1, ProbComp.expect_pure, ProbComp.expect_pure]
        exact hg₀₁ _ _ _ huv

/-- **Step M** (design r1 §3.1) [BB04, proof of Theorem 4.1]: for `g ≠ 1`, good coins
`2^{ℓ(κ)} ≤ p`, and parameters `o h` read as `(g, g^α, g^{b'}, h)`, the real game with `h` drawn
at the first `Init` simulates like the simulator on `X = g^α`, `Y = g^{b'}` with the challenge
coin `c` drawn at the first valid `Challenge`, for functions `F` of the output:
`𝔼[F ∘ fst] (simulate (bb1RealLazy … o) c (none, none)) =
𝔼[F ∘ fst] (simulate (bb1SimLazy … (fun c => (g^c, e(g, g)^{α b' c}))) c (none, none))`.

**Proof sketch.** `ProbComp.expect_simulate_rel` with `RelM`, the per-call hypothesis
`stepM_call`, functions of the output only, and `RelM` at the empty states. -/
theorem expect_simulate_bb1RealLazy (hg : g ≠ 1)
    (hp : 2 ^ (bb1Scheme G ℓ).idLen.eval κ ≤ (G.group κ d).order)
    (ho : ∀ h, RealReads G ℓ κ d g α (g ^ b'.val) h (o h)) {β : Type}
    (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β) (F : β → ℝ) :
    ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) (fun p => F p.1) =
      ProbComp.expect (simulate (bb1SimLazy G ℓ b κ d g (g ^ α.val) (g ^ b'.val)
        (fun c : ZMod (G.group κ d).order =>
          (g ^ c.val, (G.group κ d).pair g g ^ (α * b' * c).val))) c (none, none))
        (fun p => F p.1) :=
  ProbComp.expect_simulate_rel _ _ (RelM G ℓ κ d g (g ^ α.val))
    (fun i x u v huv g₀ g₁ hg₀₁ => stepM_call G ℓ b κ d o g α b' hg hp ho i x u v huv g₀ g₁ hg₀₁)
    c _ _ (fun _ _ _ _ => rfl) ⟨rfl, .none⟩

end StepM

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
