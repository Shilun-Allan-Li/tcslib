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
  sorry

/-- **Distinct `n`-bit identities are distinct in `Z_p` when `2^n ≤ p`**: reading `n`-bit strings
as numbers modulo `p` is injective, `fun u => (bitsToNat u : ZMod p)`. Glue for
[BB04, §4.4]'s condition on the identity length. -/
theorem natCast_bitsToNat_injective {n p : ℕ} (hp : 2 ^ n ≤ p) :
    Function.Injective fun u : Fin n → Bool => (bitsToNat u : ZMod p) := by
  sorry

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
  sorry

/-- **`F(ID*) = g^{α_1}`** [BB04, proof of Theorem 4.1, *Challenge*, "Since
`F_i(I^*_i) = g^{α_i}`"]: for `h = X^{−z} g^{α_1}`, `X^z · h = g^{α_1}`. -/
theorem F_target_eq (g X : B.G) (z a₁ : ZMod B.order) :
    X ^ z.val * (X ^ (-z).val * g ^ a₁.val) = g ^ a₁.val := by
  sorry

/-- **`e(g^α, g^{b'})^s = e(g, g)^{α b' s}`** [BB04, proof of Theorem 4.1, *Challenge*, "if
`T = e(g, g)^{abc} = e(g_1, g_2)^c`"]: `B.pair (g^α) (g^{b'}) ^ s.val =
B.pair g g ^ (α · b' · s).val`. -/
theorem pair_pow_val_eq (g : B.G) (α b' s : ZMod B.order) :
    B.pair (g ^ α.val) (g ^ b'.val) ^ s.val = B.pair g g ^ (α * b' * s).val := by
  sorry

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
  sorry

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
