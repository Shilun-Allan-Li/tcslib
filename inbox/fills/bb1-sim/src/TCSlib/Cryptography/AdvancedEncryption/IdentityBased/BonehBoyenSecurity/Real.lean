/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.Games.Relational

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The real IND-sID-CPA game of BB1, with `h` drawn at `Init`

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 1 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The real game draws the parameter `h` in `Setup`,
before the adversary commits to `ID*`; the simulator chooses `h = g_1^{−ID*} g^{α_1}` after the
commitment. This module moves the real draw of `h` to the first `Init`:
* `RealReads` and `setup_out` read the output of `Setup` without naming the parameters as a
  value: a map `o` from the setup's coins to parameters and master key, and what the game's
  oracles read from `o …` (the encoded parameters, the message space, the encoded keys and
  ciphertexts);
* `bb1RealAt o h` runs the game's oracles on the parameters `o h'` for the `h'` recorded with the
  committed identity, and records `h` at the first `Init`; from the empty state it simulates like
  the game's oracles on `o h` (`expect_simulate_sidImpl_bb1RealAt`, an instance of
  `ProbComp.expect_simulate_rel`);
* `bb1RealLazy o` draws `h` at the first `Init`; it simulates like `bb1RealAt o h` with `h` drawn
  in advance (`expect_sample_bb1RealAt`, an instance of `Games.expect_simulate_eager`).

## Main definitions

* `BB1Sim.RealReads` — what the game's oracles read from the parameters and master key.
* `BB1Sim.BB1RealState` — the game's state with `h` recorded beside the committed identity.
* `BB1Sim.bb1RealAt`, `BB1Sim.bb1RealLazy` — the game's oracles with `h` recorded, and with `h`
  drawn at the first `Init`.

## Main results

* `BB1Sim.setup_out` — the output of `Setup`, read.
* `BB1Sim.expect_simulate_sidImpl_bb1RealAt` — step R1: the game's oracles simulate like
  `bb1RealAt`.
* `BB1Sim.expect_sample_bb1RealAt` — step E-h: `h` drawn at the first `Init`.
* `BB1Sim.expect_sample_sidImpl` — both: the game with `h` drawn in advance simulates like
  `bb1RealLazy`.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.1 (pp. 5–6): the system;
  §4.2 (pp. 6–8): the proof of Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

/-! ### The real parameters, from the setup's output -/

section Setup

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ)

/-- **What the real game's oracles read from its parameters and master key** `k`, for parameters
`(g, g^α, Y, h)` and master key `Y^α` in the group described by `d` [BB04, §4.1]: the encoded
parameters, the message space, the encoded keys of `KeyGen`, and the encoded ciphertexts of
`Encrypt`. -/
structure RealReads (d : List Bool) (g : (G.group κ d).G) (α : ZMod (G.group κ d).order)
    (Y h : (G.group κ d).G) (k : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) : Prop where
  /-- The encoded parameters: `d ‖ g ‖ g^α ‖ Y ‖ h`. -/
  encPP : (bb1Scheme G ℓ).encPP κ k.1 = padFin ((bb1Scheme G ℓ).ppLen.eval κ)
    (d ++ List.ofFn ((G.group κ d).encG g) ++ List.ofFn ((G.group κ d).encG (g ^ α.val)) ++
      List.ofFn ((G.group κ d).encG Y) ++ List.ofFn ((G.group κ d).encG h))
  /-- The message space: the encodings of `G_T`. -/
  msgSpace : ∀ m, (bb1Scheme G ℓ).MsgSpace κ k.1 m ↔
    ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn m
  /-- `KeyGen`, encoded, then `f`: the key word is `Y^α F(ID)^r ‖ g^r` with `r` uniform. -/
  keyGen : ∀ id {β : Type} (f : (Fin ((bb1Scheme G ℓ).skLen.eval κ) → Bool) → ProbComp β),
    ((bb1Scheme G ℓ).keyGen κ k.2 id).bind (fun sk => f ((bb1Scheme G ℓ).encSK κ sk)) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun r =>
        f (padFin ((bb1Scheme G ℓ).skLen.eval κ)
          (List.ofFn ((G.group κ d).encG
              (Y ^ α.val * BB1.F ⟨g, g ^ α.val, Y, h⟩ (BB1.idToZ (G.group κ d) id) ^ r.val)) ++
            List.ofFn ((G.group κ d).encG (g ^ r.val))))
  /-- `Encrypt`, encoded, then `f`: the ciphertext word is `M · e(g^α, Y)^s ‖ g^s ‖ F(ID)^s`
  with `s` uniform, the message read at the width of `G_T`. -/
  enc : ∀ t m {β : Type} (f : (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) → ProbComp β),
    ((bb1Scheme G ℓ).enc κ k.1 t m).bind (fun ct => f ((bb1Scheme G ℓ).encCT κ ct)) =
      (ProbComp.sample (ZMod (G.group κ d).order)).bind fun s =>
        f (padFin ((bb1Scheme G ℓ).ctLen.eval κ)
          (List.ofFn ((G.group κ d).encT ((G.group κ d).pair (g ^ α.val) Y ^ s.val *
              BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m)))) ++
            List.ofFn ((G.group κ d).encG (g ^ s.val)) ++
            List.ofFn ((G.group κ d).encG
              (BB1.F ⟨g, g ^ α.val, Y, h⟩ (BB1.idToZ (G.group κ d) t) ^ s.val))))

/-- **The setup's output, read** [BB04, §4.1, *Setup*]: there is a map `o` from the setup's
coins to parameters and master key of `bb1Scheme G ℓ` such that `Setup` draws `r`, `g ∈ G^*`,
`α`, `h`, `g_2` and returns `o r g α h g_2`:
`(Setup κ).bind F = (sample r).bind … (sample g_2).bind fun g_2 => F (o r g α h g_2)` for every
continuation `F`, and the game's oracles read `o r g α h g_2` as the parameters
`(g, g^α, g_2, h)` and the master key `g_2^α` of the group `desc(κ, r)` (`RealReads`).

**Proof sketch.** `o` is the setup's output map, found by unification after reading `Setup`
through `bb1Scheme_setup_eq` and `BB1.setup_eq`. The four readings: `ofFn_bb1Scheme_encPP`;
`bb1Scheme_msgSpace_iff`; `bb1Scheme_keyGen_bind`, `BB1.keyGen_eq` and
`ofFn_bb1Scheme_encSK`; `bb1Scheme_enc_bind`, `BB1.encrypt_eq` and `ofFn_bb1Scheme_encCT`
(vectors with equal words are equal, `List.ofFn_injective`). -/
theorem setup_out :
    ∃ o : (r : G.gen.Coins κ) → {x : (G.group κ (G.desc κ r)).G // x ≠ 1} →
        ZMod (G.group κ (G.desc κ r)).order → (G.group κ (G.desc κ r)).G →
        (G.group κ (G.desc κ r)).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ,
      (∀ {β : Type} (F : (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ → ProbComp β),
        ((bb1Scheme G ℓ).setup κ).bind F =
          (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
          (ProbComp.sample {x : (G.group κ (G.desc κ r)).G // x ≠ 1}).bind fun g =>
          (ProbComp.sample (ZMod (G.group κ (G.desc κ r)).order)).bind fun α =>
          (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun h =>
          (ProbComp.sample (G.group κ (G.desc κ r)).G).bind fun g2 => F (o r g α h g2)) ∧
      ∀ r g α h g2, RealReads G ℓ κ (G.desc κ r) g.1 α g2 h (o r g α h g2) := by
  refine ⟨?o, fun F => ?hF, ?hR⟩
  case hF =>
    rw [bb1Scheme_setup_eq]
    simp only [OracleComp.bind_assoc, BB1.setup_eq, OracleComp.pure_bind]
    rfl
  case hR =>
    intro r g α h g2
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact List.ofFn_injective (ofFn_bb1Scheme_encPP G ℓ κ _ _)
    · exact fun m => bb1Scheme_msgSpace_iff G ℓ κ _ _ m
    · intro id β f
      rw [bb1Scheme_keyGen_bind, BB1.keyGen_eq, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]
      refine congrArg _ (funext fun r => ?_)
      rw [List.ofFn_injective (ofFn_bb1Scheme_encSK G ℓ κ _ _)]
    · intro t m β f
      rw [bb1Scheme_enc_bind, BB1.encrypt_eq, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]
      refine congrArg _ (funext fun s => ?_)
      rw [List.ofFn_injective (ofFn_bb1Scheme_encCT G ℓ κ _ _)]

end Setup

/-! ### The game's oracles with `h` recorded -/

section Real

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- The real game's state with the parameter `h` recorded beside the committed identity, and
the recorded challenge. -/
abbrev BB1RealState (κ : ℕ) (d : List Bool) : Type :=
  Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × (G.group κ d).G) ×
    Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)

/-- **The game's oracles with `h` recorded** [BB04, §2.1]: with hidden bit `b`, on the
parameters and master key `o h'` for the `h'` recorded with the committed identity (or `h`
before `Init`), the call of `IBEScheme.sidImpl` on the state without `h'`; the first `Init`
records `h` with the identity. -/
noncomputable def bb1RealAt (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1RealState G ℓ κ d) unifSpec :=
  fun i x u => ((bb1Scheme G ℓ).sidImpl b κ (o ((u.1.map Prod.snd).getD h)).1
    (o ((u.1.map Prod.snd).getD h)).2 i x (u.1.map Prod.fst, u.2)).bind
      fun p => .pure (p.1, (p.2.1.map fun t => (t, (u.1.map Prod.snd).getD h), p.2.2))

/-- Before `Init`, `bb1RealAt o h` is the game's oracle on `o h`, recording `h` with the
committed identity: `bb1RealAt … o h i x (none, c) = (sidImpl b κ (o h).1 (o h).2 i x
(none, c)).bind fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. -/
theorem bb1RealAt_none (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G)
    (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealAt G ℓ b κ d o h i x (none, c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (none, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := rfl

/-- After `Init`, `bb1RealAt o h` is the game's oracle on `o h'` for the recorded `h'`:
`bb1RealAt … o h i x (some (t, h'), c) = (sidImpl b κ (o h').1 (o h').2 i x
(some t, c)).bind fun p => pure (p.1, (p.2.1.map (·, h'), p.2.2))`. -/
theorem bb1RealAt_some (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) (h : (G.group κ d).G)
    (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h' : (G.group κ d).G)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealAt G ℓ b κ d o h i x (some (t, h'), c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o h').1 (o h').2 i x (some t, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h'), p.2.2)) := rfl

open Classical in
/-- **The game's oracles with `h` drawn at the first `Init`** [BB04, §2.1]: the first `Init`
draws `h ∈ G` and calls `bb1RealAt o h`; every other call is the call of `bb1RealAt o 1`, which
reads the recorded `h'` after `Init` and no parameter before it. -/
noncomputable def bb1RealLazy (b : Bool) (κ : ℕ) (d : List Bool)
    (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1RealState G ℓ κ d) unifSpec :=
  fun i x u => if u.1.isNone ∧ i = 0 then
      (ProbComp.sample (G.group κ d).G).bind fun h => bb1RealAt G ℓ b κ d o h i x u
    else bb1RealAt G ℓ b κ d o 1 i x u

variable (b : Bool) (κ : ℕ) (d : List Bool)
  (o : (G.group κ d).G → (bb1Scheme G ℓ).PP κ × (bb1Scheme G ℓ).MSK κ)

/-- The first `Init` of `bb1RealLazy` draws `h` and calls the game's oracle on `o h`:
`bb1RealLazy … o 0 x (none, c) = (sample G).bind fun h => (sidImpl b κ (o h).1 (o h).2 0 x
(none, c)).bind fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. -/
theorem bb1RealLazy_zero_none (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealLazy G ℓ b κ d o 0 x (none, c) =
      (ProbComp.sample (G.group κ d).G).bind fun h =>
        ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 0 x (none, c)).bind
          fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := by
  rw [bb1RealLazy, if_pos ⟨rfl, rfl⟩]
  rfl

/-- Before `Init`, the other calls of `bb1RealLazy` are the game's oracles on `o 1`: for `i ≠ 0`,
`bb1RealLazy … o i x (none, c) = (sidImpl b κ (o 1).1 (o 1).2 i x (none, c)).bind fun p =>
pure (p.1, (p.2.1.map (·, 1), p.2.2))`. -/
theorem bb1RealLazy_none_of_ne (i : Fin 3) (hi : i ≠ 0) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealLazy G ℓ b κ d o i x (none, c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o 1).1 (o 1).2 i x (none, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, 1), p.2.2)) := by
  rw [bb1RealLazy, if_neg fun h => hi h.2]
  rfl

/-- After `Init`, `bb1RealLazy` is the game's oracle on `o h` for the recorded `h`:
`bb1RealLazy … o i x (some (t, h), c) = (sidImpl b κ (o h).1 (o h).2 i x (some t, c)).bind
fun p => pure (p.1, (p.2.1.map (·, h), p.2.2))`. -/
theorem bb1RealLazy_some (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (h : (G.group κ d).G)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    bb1RealLazy G ℓ b κ d o i x (some (t, h), c) =
      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (some t, c)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) := by
  rw [bb1RealLazy, if_neg fun h => absurd h.1 (by simp)]
  rfl

/-- **The game's oracles keep the committed identity**: for every scheme `S`, every outcome of
`S.sidImpl b κ pp msk i x (some t, c)` has the committed identity `t`.

**Proof sketch.** By cases on the oracle, read through `IBEScheme.sidImpl_zero_onSpec`,
`sidImpl_one_onQuery`, `sidImpl_two_onQuery`, `sidImpl_keyGen_ne_onSpec` and
`sidImpl_challenge_fresh_onSpec`: `Init` keeps the state (`sidImpl_init_some`), `KeyGen` keeps it
(`sidImpl_keyGen_target`, `sidImpl_keyGen_ne`), and `Challenge` keeps `ID*` and records the
challenge at most (`sidImpl_challenge_fresh`, `_invalid`, `_repeat`). -/
theorem sidImpl_allOutputs_some (S : IBEScheme) (pp : S.PP κ) (msk : S.MSK κ) (i : Fin 3)
    (x : (S.sidSpec κ).dom i) (t : Fin (S.idLen.eval κ) → Bool)
    (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    (S.sidImpl b κ pp msk i x (some t, c)).AllOutputs fun p => p.2.1 = some t := by
  have h012 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases h012 i with rfl | rfl | rfl
  · rw [IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_some, OracleComp.pure_bind]
    exact OracleComp.allOutputs_pure.2 rfl
  · by_cases ht : cast (sidSpec_dom_one S κ) x = t
    · rw [IBEScheme.sidImpl_one_onQuery, ht, IBEScheme.sidImpl_keyGen_target]
      exact OracleComp.allOutputs_pure.2 rfl
    · rw [IBEScheme.sidImpl_keyGen_ne_onSpec S b κ pp msk x t c ht]
      apply OracleComp.AllOutputs.bind (P := fun _ => True) (OracleComp.allOutputs_true _)
      intro _ _
      exact OracleComp.allOutputs_pure.2 rfl
  · rcases c with _ | w
    · by_cases hv : S.MsgSpace κ pp
          (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).1 ∧
        S.MsgSpace κ pp (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two S κ) x)).2
      · rw [IBEScheme.sidImpl_challenge_fresh_onSpec S b κ pp msk x t hv]
        apply OracleComp.AllOutputs.bind (P := fun _ => True) (OracleComp.allOutputs_true _)
        intro _ _
        exact OracleComp.allOutputs_pure.2 rfl
      · rw [IBEScheme.sidImpl_two_onQuery, IBEScheme.sidImpl_challenge_invalid (h := hv)]
        exact OracleComp.allOutputs_pure.2 rfl
    · rw [IBEScheme.sidImpl_two_onQuery, IBEScheme.sidImpl_challenge_repeat]
      exact OracleComp.allOutputs_pure.2 rfl

/-- **Before `Init`, `KeyGen` and `Challenge` do not read the parameters**: for every scheme `S`
and `i ≠ 0`, `S.sidImpl b κ pp msk i x (none, c) = S.sidImpl b κ pp' msk' i x (none, c)`, and
every outcome keeps the state `(none, c)`. -/
theorem sidImpl_none_of_ne (S : IBEScheme) (pp pp' : S.PP κ) (msk msk' : S.MSK κ) (i : Fin 3)
    (hi : i ≠ 0) (x : (S.sidSpec κ).dom i) (c : Option (Fin (S.ctLen.eval κ) → Bool)) :
    S.sidImpl b κ pp msk i x (none, c) = S.sidImpl b κ pp' msk' i x (none, c) ∧
      (S.sidImpl b κ pp msk i x (none, c)).AllOutputs fun p => p.2 = (none, c) := by
  have h12 : ∀ i : Fin 3, i ≠ 0 → i = 1 ∨ i = 2 := by decide
  rcases h12 i hi with rfl | rfl
  · rw [IBEScheme.sidImpl_one_onQuery S b κ pp msk x,
      IBEScheme.sidImpl_one_onQuery S b κ pp' msk' x, IBEScheme.sidImpl_keyGen_none,
      IBEScheme.sidImpl_keyGen_none]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩
  · rw [IBEScheme.sidImpl_two_onQuery S b κ pp msk x,
      IBEScheme.sidImpl_two_onQuery S b κ pp' msk' x, IBEScheme.sidImpl_challenge_none,
      IBEScheme.sidImpl_challenge_none]
    exact ⟨rfl, OracleComp.allOutputs_pure.2 rfl⟩

/-- **Step R1** (design r1 §3.1): from the empty state, the game's oracles on `o h` simulate like
`bb1RealAt o h`, for functions `F` of the output:
`𝔼[F ∘ fst] (simulate (sidImpl b κ (o h).1 (o h).2) c (none, none)) =
𝔼[F ∘ fst] (simulate (bb1RealAt … o h) c (none, none))`. Glue: an instance of
`ProbComp.expect_simulate_rel` with `R s u :↔ s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h`.

**Proof sketch.** From related states, `bb1RealAt o h` reads the recorded `h' = h`, so its call
is the game's call followed by recording `h` (`bb1RealAt_none`, `bb1RealAt_some`); its
expectation is the game's call's (`expect_bind`, `expect_pure`), whose new states are related
to the recorded ones. `ProbComp.expect_simulate_rel` concludes. -/
theorem expect_simulate_sidImpl_bb1RealAt (h : (G.group κ d).G) {α : Type}
    (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α) (F : α → ℝ) :
    ProbComp.expect (simulate ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2) c (none, none))
        (fun p => F p.1) =
      ProbComp.expect (simulate (bb1RealAt G ℓ b κ d o h) c (none, none)) (fun p => F p.1) := by
  refine ProbComp.expect_simulate_rel _ _
    (fun s u => s = (u.1.map Prod.fst, u.2) ∧ ∀ p ∈ u.1, p.2 = h) (fun i x s u hsu g₀ g₁ hg => ?_)
    c _ _ (fun _ _ _ _ => rfl) ⟨rfl, fun p hp => by cases hp⟩
  obtain ⟨rfl, hh⟩ := hsu
  -- from related states, `bb1RealAt h` reads the recorded `h`
  have hget : (u.1.map Prod.snd).getD h = h := by
    rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    · rfl
    · exact hh _ rfl
  rw [show bb1RealAt G ℓ b κ d o h i x u =
      ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2 i x (u.1.map Prod.fst, u.2)).bind
        fun p => .pure (p.1, (p.2.1.map fun t => (t, h), p.2.2)) by rw [bb1RealAt, hget],
    ProbComp.expect_bind]
  refine congrArg _ (funext fun p => ?_)
  rw [ProbComp.expect_pure]
  refine hg p.1 p.2 _ ⟨?_, fun q hq => ?_⟩ <;> rcases p with ⟨a, _ | t, c⟩
  · rfl
  · rfl
  · cases hq
  · cases hq
    rfl

/-- **Step E-h** (design r1 §3.1): `h` drawn in advance or at the first `Init` simulate alike:
`𝔼_{h ← G} 𝔼[F] (simulate (bb1RealAt … o h) c (none, none)) =
𝔼[F] (simulate (bb1RealLazy … o) c (none, none))`. Glue: an instance of
`Games.expect_simulate_eager`, with `h` spent at the first `Init`.

**Proof sketch.** Apply `Games.expect_simulate_eager` with `O := bb1RealLazy o`,
`OE h := bb1RealAt o h` and `used u := u.1` some. After `Init` both read the recorded `h`
(`bb1RealAt_some`, `bb1RealLazy_some`) and keep the identity (`sidImpl_allOutputs_some`). Before
`Init`, `KeyGen` and `Challenge` read no parameter and keep the state (`sidImpl_none_of_ne`,
`bb1RealLazy_none_of_ne`); the first `Init` draws `h` (`bb1RealLazy_zero_none`) and records an
identity (`IBEScheme.sidImpl_zero_onSpec`, `IBEScheme.sidImpl_init_none`). -/
theorem expect_sample_bb1RealAt {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
    (F : α × BB1RealState G ℓ κ d → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).G)
        (fun h => ProbComp.expect (simulate (bb1RealAt G ℓ b κ d o h) c (none, none)) F) =
      ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) F := by
  refine (Games.expect_simulate_eager (T := (G.group κ d).G) (bb1RealLazy G ℓ b κ d o)
    (bb1RealAt G ℓ b κ d o) (fun u => u.1.isSome = true) (fun h i x u hu => ?_)
    (fun i x u hu => ?_) (fun i x u hu => ?_) c F
    (by show ¬ ((none : Option _).isSome = true); exact Bool.false_ne_true)).symm
  -- after `Init`, both read the recorded `h`
  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    · exact absurd hu Bool.false_ne_true
    · rw [bb1RealAt_some, bb1RealLazy_some]
  -- the committed identity stays committed
  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    · exact absurd hu Bool.false_ne_true
    · rw [bb1RealLazy_some]
      exact (sidImpl_allOutputs_some b κ _ _ _ i x t c).bind fun p hp =>
        OracleComp.allOutputs_pure.2 (by show (p.2.1.map _).isSome = true; rw [hp]; rfl)
  -- before `Init`: the first `Init` draws `h`; `KeyGen` and `Challenge` read no parameter
  · rcases u with ⟨_ | ⟨t, h'⟩, c⟩
    swap
    · exact absurd rfl hu
    by_cases hi : i = 0
    · subst hi
      refine Or.inr ⟨?_, fun h => ?_⟩
      · rw [bb1RealLazy_zero_none]
        exact congrArg _ (funext fun h => (bb1RealAt_none G ℓ b κ d o h 0 x c).symm)
      · rw [bb1RealAt_none, IBEScheme.sidImpl_zero_onSpec, IBEScheme.sidImpl_init_none,
          OracleComp.pure_bind, OracleComp.pure_bind]
        exact OracleComp.allOutputs_pure.2 rfl
    · have hn := fun h => sidImpl_none_of_ne b κ (bb1Scheme G ℓ) (o h).1 (o 1).1 (o h).2 (o 1).2
        i hi x c
      refine Or.inl fun h => ⟨?_, ?_⟩
      · rw [bb1RealAt_none, bb1RealLazy_none_of_ne G ℓ b κ d o i hi x c, (hn h).1]
        exact OracleComp.bind_congr_of_allOutputs (hn 1).2 fun p hp => by rw [hp]; rfl
      · rw [bb1RealLazy_none_of_ne G ℓ b κ d o i hi x c]
        exact (sidImpl_none_of_ne b κ _ (o 1).1 (o 1).1 (o 1).2 (o 1).2 i hi x c).2.bind
          fun p hp => OracleComp.allOutputs_pure.2 (by
            show ¬ ((p.2.1.map _).isSome = true); rw [hp]; exact Bool.false_ne_true)

/-- **The real game with `h` drawn at the first `Init`** (steps R1 and E-h of design r1 §3.1):
`𝔼_{h ← G} 𝔼[F ∘ fst] (simulate (sidImpl b κ (o h).1 (o h).2) c (none, none)) =
𝔼[F ∘ fst] (simulate (bb1RealLazy … o) c (none, none))`. Glue.

**Proof sketch.** `expect_simulate_sidImpl_bb1RealAt` for each `h`, then
`expect_sample_bb1RealAt`. -/
theorem expect_sample_sidImpl {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
    (F : α → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).G)
        (fun h => ProbComp.expect
          (simulate ((bb1Scheme G ℓ).sidImpl b κ (o h).1 (o h).2) c (none, none))
          (fun p => F p.1)) =
      ProbComp.expect (simulate (bb1RealLazy G ℓ b κ d o) c (none, none)) (fun p => F p.1) := by
  rw [← expect_sample_bb1RealAt]
  exact congrArg _ (funext fun h => expect_simulate_sidImpl_bb1RealAt G ℓ b κ d o h c F)

end Real

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
