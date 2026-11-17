/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Tools

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator with its exponents drawn from coin blocks

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The simulator `bb1SimImpl` of
`AdvancedEncryption/IdentityBased/BonehBoyen.lean` draws its exponents `α_1` and `r` uniformly
from `Z_p`. The reduction machine draws them from blocks of fresh coins instead, by the rejection
sampler `Candidates.sampleBelowL p (Nat.size p) n n` with `n = κ + wG(κ) + 1` and the fallback
`0` (`draw`), which is within `(1/2)^n` of uniform (`statClose_draw`). The bounded sampler and
its bound are the library's existing construction, `Candidates.sampleBelowL` and
`Candidates.statClose_sampleBelowL` (`Cryptography/Candidates/DiscreteLog.lean`): for
`0 < m < 2^n` its output on `n · n` uniform coins, with the fallback `0`, is within `(1/2)^n` of
the uniform number below `m`. This file gives
* the simulator's oracles with the exponent supplied as an argument (`drawStep`), on the
  query and answer lengths of the machine (`qLen`, `aLen`), with their case lemmas;
* the comparison of drawn and ideal exponents on a deterministic run: for a test with values
  `0` and `1` of `cap` exponents, `cap` drawn exponents change its average by at most
  `cap · (1/2)^n` (`abs_expect_draws_sub_le`, from `statClose_draw` and
  `OneWay.statClose_pi`);
* determinism of the run of `drawStep` with exponents read from a tape
  (`exists_simulate_tape_eq_pure`).

## Main definitions

* `BB1Machine.qLen`, `BB1Machine.aLen` — the query and answer lengths of the three oracles.
* `BB1Machine.blockLen` — the sampler's width `n = κ + wG(κ) + 1`.
* `BB1Machine.draw` — an exponent of `Z_p` drawn from `n · n` coins.
* `BB1Machine.drawStep` — the simulator's oracles with the exponent given.

## Main results

* `BB1Machine.qLen_eval`, `BB1Machine.aLen_eval` — the lengths are the game's.
* `BB1Machine.statClose_draw` — a drawn exponent is `(1/2)^n`-close to uniform.
* `BB1Machine.drawStep_zero`, `BB1Machine.drawStep_one_none`, …,
  `BB1Machine.drawStep_two_invalid` — the case lemmas.
* `BB1Machine.exists_drawStep_eq_pure`, `BB1Machine.exists_simulate_tape_eq_pure` — the oracles
  and their runs from a tape are deterministic.
* `BB1Machine.abs_expect_draws_sub_le` — drawn against ideal exponents.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the simulator
  in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 181.1, statistical closeness. Context only: §2.8, Theorem 52.3, the discrete-log
  collection, whose proof remarks that its domain `Z_q` is easy to sample; it does not give
  this sampler, its coin budget, its fallback or its bound, which are the library's
  `Candidates.sampleBelowL` and `Candidates.statClose_sampleBelowL`.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Machine

variable (G : BilinearGen) (ℓ : PolyExpr)

/-! ### Lengths -/

/-- The query lengths of the three oracles as polynomials: identities for `Init` (`0`) and
`KeyGen` (`1`), two messages for `Challenge` (`2`). -/
noncomputable def qLen : Fin 3 → PolyExpr
  | 0 => (bb1Scheme G ℓ).idLen
  | 1 => (bb1Scheme G ℓ).idLen
  | 2 => (bb1Scheme G ℓ).msgLen.add (bb1Scheme G ℓ).msgLen

/-- `qLen G ℓ 0 = idLen`. -/
theorem qLen_zero : qLen G ℓ 0 = (bb1Scheme G ℓ).idLen := rfl

/-- `qLen G ℓ 1 = idLen`. -/
theorem qLen_one : qLen G ℓ 1 = (bb1Scheme G ℓ).idLen := rfl

/-- `qLen G ℓ 2 = msgLen + msgLen`. -/
theorem qLen_two : qLen G ℓ 2 = (bb1Scheme G ℓ).msgLen.add (bb1Scheme G ℓ).msgLen := rfl

/-- The answer lengths of the three oracles as polynomials: parameters for `Init`, a validity
bit and a key for `KeyGen`, a ciphertext for `Challenge`. -/
noncomputable def aLen : Fin 3 → PolyExpr
  | 0 => (bb1Scheme G ℓ).ppLen
  | 1 => (bb1Scheme G ℓ).skLen.add (.const 1)
  | 2 => (bb1Scheme G ℓ).ctLen

/-- `aLen G ℓ 0 = ppLen`. -/
theorem aLen_zero : aLen G ℓ 0 = (bb1Scheme G ℓ).ppLen := rfl

/-- `aLen G ℓ 1 = skLen + 1`. -/
theorem aLen_one : aLen G ℓ 1 = (bb1Scheme G ℓ).skLen.add (.const 1) := rfl

/-- `aLen G ℓ 2 = ctLen`. -/
theorem aLen_two : aLen G ℓ 2 = (bb1Scheme G ℓ).ctLen := rfl

/-- The query lengths are the game's: `(qLen G ℓ ·).eval κ = (bb1Scheme G ℓ).inLens κ`. -/
theorem qLen_eval (κ : ℕ) : (fun i => (qLen G ℓ i).eval κ) = (bb1Scheme G ℓ).inLens κ := by
  funext i
  match i with
  | 0 => rw [qLen_zero, IBEScheme.inLens_zero]
  | 1 => rw [qLen_one, IBEScheme.inLens_one]
  | 2 => rw [qLen_two, PolyExpr.eval_add, IBEScheme.inLens_two]

/-- The answer lengths are the game's: `(aLen G ℓ ·).eval κ = (bb1Scheme G ℓ).outLens κ`. -/
theorem aLen_eval (κ : ℕ) : (fun i => (aLen G ℓ i).eval κ) = (bb1Scheme G ℓ).outLens κ := by
  funext i
  match i with
  | 0 => rw [aLen_zero, IBEScheme.outLens_zero]
  | 1 => rw [aLen_one, PolyExpr.eval_add, PolyExpr.eval_const, IBEScheme.outLens_one]
  | 2 => rw [aLen_two, IBEScheme.outLens_two]

/-! ### Exponents drawn from coins -/

/-- The width `n = κ + wG(κ) + 1` of the exponent sampler (Gate 40, G40-03): `n` trials of
`n`-bit blocks. -/
def blockLen : PolyExpr := (PolyExpr.var.add G.wG).add (.const 1)

/-- `(blockLen G).eval κ = κ + wG(κ) + 1`. -/
theorem blockLen_eval (κ : ℕ) : (blockLen G).eval κ = κ + G.wG.eval κ + 1 := by
  rw [blockLen, PolyExpr.eval_add, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]

/-- **An exponent of `Z_p` drawn from `n · n` coins**: the library's bounded rejection sampler
`Candidates.sampleBelowL p (Nat.size p) n n` (`Cryptography/Candidates/DiscreteLog.lean`, whose
bound `Candidates.statClose_sampleBelowL` gives `statClose_draw`) with the fallback `0`, read in
`Z_p`, for the order `p` of the group described by `d` and `n = blockLen G κ`. That `Z_p` is
easy to sample is the remark in the proof of [PS10, Theorem 52.3] (§2.8), context only. -/
noncomputable def draw (κ : ℕ) (d : List Bool)
    (w : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) : ZMod (G.group κ d).order :=
  ((Candidates.sampleBelowL (G.group κ d).order (Nat.size (G.group κ d).order)
    ((blockLen G).eval κ) ((blockLen G).eval κ) (List.ofFn w)).getD 0 : ℕ)

/-- `draw G κ d w = ((sampleBelowL p (Nat.size p) n n ⟦w⟧).getD 0 : Z_p)`. -/
theorem draw_eq (κ : ℕ) (d : List Bool)
    (w : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) :
    draw G κ d w = ((Candidates.sampleBelowL (G.group κ d).order
      (Nat.size (G.group κ d).order) ((blockLen G).eval κ) ((blockLen G).eval κ)
      (List.ofFn w)).getD 0 : ℕ) := rfl

/-- The order of a bilinear group with `wG`-bit encodings is at most `2^{wG}`:
`(G.group κ d).order ≤ 2 ^ wG(κ)` (the encoding of `G` is injective). -/
theorem order_le_two_pow (κ : ℕ) (d : List Bool) : (G.group κ d).order ≤ 2 ^ G.wG.eval κ := by
  rw [← (G.group κ d).card_G]
  calc Fintype.card (G.group κ d).G ≤ Fintype.card (Fin (G.wG.eval κ) → Bool) :=
        Fintype.card_le_of_injective _ (G.group κ d).encG_injective
    _ = 2 ^ G.wG.eval κ := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- **A drawn exponent is `(1/2)^n`-close to uniform** on `Z_p` (Gate 40, G40-03): `0 < p` and
`p ≤ 2^{wG(κ)} < 2^n`, so `statClose_sampleBelowL` applies.

**Proof sketch.** `statClose_sampleBelowL` with `m = p`, mapped into `Z_p` by the cast
(`StatClose.map`); the uniform element of `Fin p` cast into `Z_p` is the uniform element of `Z_p`
along the bijection `x ↦ x.val` (`StatClose.comp_equiv_right`, `ZMod.natCast_zmod_val`). -/
theorem statClose_draw (κ : ℕ) (d : List Bool) :
    StatClose (draw G κ d) (id : ZMod (G.group κ d).order → ZMod (G.group κ d).order)
      ((1 / 2 : ℝ) ^ (blockLen G).eval κ) := by
  set p := (G.group κ d).order with hp
  have hm : 0 < p := (G.group κ d).order_prime.pos
  have hmn : p < 2 ^ (blockLen G).eval κ := by
    rw [blockLen_eval]
    calc p ≤ 2 ^ G.wG.eval κ := order_le_two_pow G κ d
      _ < 2 ^ (κ + G.wG.eval κ + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  let e : ZMod p ≃ Fin p :=
    { toFun := fun t => ⟨t.val, ZMod.val_lt t⟩
      invFun := fun x => ((x : ℕ) : ZMod p)
      left_inv := fun t => ZMod.natCast_zmod_val t
      right_inv := fun x => Fin.ext (by
        show ((x : ℕ) : ZMod p).val = x
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt x.2]) }
  have h := ((Candidates.statClose_sampleBelowL hm hmn).map
    fun v : ℕ => (v : ZMod p)).comp_equiv_right e
  have hX : (fun b : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool =>
      (((Candidates.sampleBelowL p (Nat.size p) ((blockLen G).eval κ) ((blockLen G).eval κ)
        (List.ofFn b)).getD 0 : ℕ) : ZMod p)) = draw G κ d :=
    funext fun b => (draw_eq G κ d b).symm
  have hY : (fun t : ZMod p => (((e t : Fin p) : ℕ) : ZMod p)) = id :=
    funext fun t => ZMod.natCast_zmod_val t
  rw [hX, hY] at h
  exact h

/-! ### The simulator's oracles with the exponent given -/

open Classical in
/-- **The simulator's oracles with the exponent `u` supplied**, on the lengths `qLen`, `aLen`,
answering with the words of BB1's encodings: the oracles of `bb1SimImpl` [BB04, proof of
Theorem 4.1] with the uniform exponent replaced by `u`.
* `Init` on `ID`: with `(ID*, α_1)` the recorded pair, or `(ID, u)` before a commitment (which it
  records), the word `d ‖ g ‖ X ‖ Y ‖ h` of the parameters `(g, X, Y, h)`,
  `h = X^{(−ID*).val} · g^{α_1.val}`.
* `KeyGen` on `ID`: `⊥` before `Init` or for `ID = ID*`; otherwise `1 ‖ d_0 ‖ d_1` with
  `d_0 = Y^{(−α_1/(ID − ID*)).val} · F(ID)^{u.val}`, `F(ID) = X^{ID.val} · h`, and
  `d_1 = Y^{(−1/(ID − ID*)).val} · g^{u.val}`.
* `Challenge` on `M_0 ‖ M_1`: `⊥` before `Init`; the recorded challenge once there is one;
  otherwise, if both halves are encodings of `G_T`, the word `M_b · T ‖ Z ‖ Z^{α_1.val}`, recorded;
  `⊥` if not.
Identities are read in `Z_p` by `BB1.idToZ` and messages decoded by `BB1.decodeT`. -/
noncomputable def drawStep (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)
    (T : (G.group κ d).GT) :
    ∀ i : Fin 3, (Fin ((qLen G ℓ i).eval κ) → Bool) → BB1SimState G ℓ κ d →
      ZMod (G.group κ d).order →
        ProbComp ((Fin ((aLen G ℓ i).eval κ) → Bool) × BB1SimState G ℓ κ d)
  | 0, x, s, u =>
    .pure (padFin _ (d ++ List.ofFn ((G.group κ d).encG g) ++ List.ofFn ((G.group κ d).encG X) ++
        List.ofFn ((G.group κ d).encG Y) ++ List.ofFn ((G.group κ d).encG
          (X ^ (-BB1.idToZ (G.group κ d) (s.1.getD (padFin _ (List.ofFn x), u)).1).val *
            g ^ (s.1.getD (padFin _ (List.ofFn x), u)).2.val))),
      (some (s.1.getD (padFin _ (List.ofFn x), u)), s.2))
  | 1, x, s, u =>
    match s.1 with
    | some (t, α₁) =>
      if List.ofFn x = List.ofFn t then .pure (zeroBits _, s)
      else .pure (padFin _ (true :: (List.ofFn ((G.group κ d).encG
          (Y ^ (-α₁ / (BB1.idToZ (G.group κ d)
              (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val *
            (X ^ (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x))).val *
              (X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)) ^ u.val)) ++
          List.ofFn ((G.group κ d).encG
            (Y ^ (-1 / (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val * g ^ u.val)))), s)
    | none => .pure (zeroBits _, s)
  | 2, mm, s, _ =>
    match s.1, s.2 with
    | some _, some c => .pure (padFin _ (List.ofFn c), s)
    | some (_, α₁), none =>
      if (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)) then
        .pure (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d)
            (padFin _ (if b then (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val))),
          (s.1, some (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d)
            (padFin _ (if b then (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val))))))
      else .pure (zeroBits _, s)
    | none, _ => .pure (zeroBits _, s)

section Cases

variable (b : Bool) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G) (T : (G.group κ d).GT)

/-- **`Init`**: with `(t, α) = s.1.getD (ID, u)` (the recorded pair, or the query and `u` before a
commitment), the answer is the padded word `d ‖ g ‖ X ‖ Y ‖ X^{(−t).val} g^{α.val}` and the state
records `(t, α)`. -/
theorem drawStep_zero (x : Fin ((qLen G ℓ 0).eval κ) → Bool) (s : BB1SimState G ℓ κ d)
    (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 0 x s u =
      .pure (padFin _ (d ++ List.ofFn ((G.group κ d).encG g) ++
          List.ofFn ((G.group κ d).encG X) ++ List.ofFn ((G.group κ d).encG Y) ++
          List.ofFn ((G.group κ d).encG
            (X ^ (-BB1.idToZ (G.group κ d) (s.1.getD (padFin _ (List.ofFn x), u)).1).val *
              g ^ (s.1.getD (padFin _ (List.ofFn x), u)).2.val))),
        (some (s.1.getD (padFin _ (List.ofFn x), u)), s.2)) :=
  rfl

/-- **`KeyGen` before `Init`** answers `⊥` and keeps the state. -/
theorem drawStep_one_none (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 1 x (none, c) u = .pure (zeroBits _, (none, c)) :=
  rfl

/-- **`KeyGen` for the committed identity** (equal words) answers `⊥` and keeps the state. -/
theorem drawStep_one_target (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order)
    (h : List.ofFn x = List.ofFn t) :
    drawStep G ℓ b κ d g X Y Z T 1 x (some (t, α₁), c) u =
      .pure (zeroBits _, (some (t, α₁), c)) := by
  show (if List.ofFn x = List.ofFn t then _ else _) = _
  rw [if_pos h]

/-- **`KeyGen` for another identity** answers the padded word `1 ‖ d_0 ‖ d_1` of the simulated
key with `r = u` and keeps the state.

**Proof sketch.** The committed branch of `drawStep` at index `1` is the test `⟦x⟧ = ⟦t⟧`;
it fails by `h`. -/
theorem drawStep_one_key (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order)
    (h : List.ofFn x ≠ List.ofFn t) :
    drawStep G ℓ b κ d g X Y Z T 1 x (some (t, α₁), c) u =
      .pure (padFin _ (true :: (List.ofFn ((G.group κ d).encG
          (Y ^ (-α₁ / (BB1.idToZ (G.group κ d)
              (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val *
            (X ^ (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x))).val *
              (X ^ (-BB1.idToZ (G.group κ d) t).val * g ^ α₁.val)) ^ u.val)) ++
          List.ofFn ((G.group κ d).encG
            (Y ^ (-1 / (BB1.idToZ (G.group κ d)
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ d) t)).val * g ^ u.val)))), (some (t, α₁), c)) := by
  show (if List.ofFn x = List.ofFn t then _ else _) = _
  rw [if_neg h]

/-- **`Challenge` before `Init`** answers `⊥` and keeps the state. -/
theorem drawStep_two_none (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (c : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (none, c) u = .pure (zeroBits _, (none, c)) :=
  rfl

/-- **`Challenge` after a recorded challenge** repeats it. -/
theorem drawStep_two_repeat (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (tα : (Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)
    (w : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) (u : ZMod (G.group κ d).order) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (some tα, some w) u =
      .pure (padFin _ (List.ofFn w), (some tα, some w)) :=
  rfl

open Classical in
/-- **The first `Challenge` with both halves in `G_T`** answers and records the padded word
`M_b · T ‖ Z ‖ Z^{α_1.val}`, `M_b` the decoded half selected by `b`.

**Proof sketch.** The branch of `drawStep` at index `2` with a commitment and no recorded
challenge is the test that both halves encode elements of `G_T`; it holds by `h`. -/
theorem drawStep_two_fresh (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (u : ZMod (G.group κ d).order)
    (h : (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ))) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (some (t, α₁), none) u =
      .pure (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT (G.group κ d)
            (padFin _ (if b then (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++ List.ofFn ((G.group κ d).encG (Z ^ α₁.val))),
          (some (t, α₁), some (padFin _ (List.ofFn ((G.group κ d).encT (BB1.decodeT
            (G.group κ d) (padFin _ (if b then (List.ofFn mm).drop
              ((bb1Scheme G ℓ).msgLen.eval κ) else (List.ofFn mm).take
                ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
            List.ofFn ((G.group κ d).encG Z) ++
              List.ofFn ((G.group κ d).encG (Z ^ α₁.val)))))) := by
  show (if _ then _ else _) = _
  rw [if_pos h]

open Classical in
/-- **The first `Challenge` with a half outside `G_T`** answers `⊥` and keeps the state. -/
theorem drawStep_two_invalid (mm : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (t : Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) (α₁ : ZMod (G.group κ d).order)
    (u : ZMod (G.group κ d).order)
    (h : ¬ ((∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ d).encT v) =
            (List.ofFn mm).drop ((bb1Scheme G ℓ).msgLen.eval κ)))) :
    drawStep G ℓ b κ d g X Y Z T 2 mm (some (t, α₁), none) u =
      .pure (zeroBits _, (some (t, α₁), none)) := by
  show (if _ then _ else _) = _
  rw [if_neg h]

/-- **The oracles with the exponent given are deterministic**: every call returns one answer and
one new state.

**Proof sketch.** Cases on the oracle, the commitment, the recorded challenge and the tests, each
closed by its case lemma (`drawStep_zero`, `drawStep_one_none`, `drawStep_one_target`,
`drawStep_one_key`, `drawStep_two_none`, `drawStep_two_fresh`, `drawStep_two_invalid`,
`drawStep_two_repeat`). -/
theorem exists_drawStep_eq_pure (i : Fin 3) (x : Fin ((qLen G ℓ i).eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) (u : ZMod (G.group κ d).order) :
    ∃ y s', drawStep G ℓ b κ d g X Y Z T i x s u = .pure (y, s') := by
  classical
  obtain ⟨o, c⟩ := s
  match i, x with
  | 0, x => exact ⟨_, _, drawStep_zero G ℓ b κ d g X Y Z T x (o, c) u⟩
  | 1, x =>
    rcases o with _ | ⟨t, α₁⟩
    · exact ⟨_, _, drawStep_one_none G ℓ b κ d g X Y Z T x c u⟩
    · by_cases h : List.ofFn x = List.ofFn t
      · exact ⟨_, _, drawStep_one_target G ℓ b κ d g X Y Z T x t α₁ c u h⟩
      · exact ⟨_, _, drawStep_one_key G ℓ b κ d g X Y Z T x t α₁ c u h⟩
  | 2, x =>
    rcases o with _ | ⟨t, α₁⟩
    · exact ⟨_, _, drawStep_two_none G ℓ b κ d g X Y Z T x c u⟩
    · rcases c with _ | w
      · by_cases h : (∃ v, List.ofFn ((G.group κ d).encT v) =
              (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
            (∃ v, List.ofFn ((G.group κ d).encT v) =
              (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))
        · exact ⟨_, _, drawStep_two_fresh G ℓ b κ d g X Y Z T x t α₁ u h⟩
        · exact ⟨_, _, drawStep_two_invalid G ℓ b κ d g X Y Z T x t α₁ u h⟩
      · exact ⟨_, _, drawStep_two_repeat G ℓ b κ d g X Y Z T x (t, α₁) w u⟩

/-- **Runs from a tape are deterministic**: with the exponent of the `j`-th query read from a
tape `V j` (`ETTGame.tapeImpl`), the run of any computation returns one output and one final
state.

**Proof sketch.** Induction on the computation; each call is deterministic
(`exists_drawStep_eq_pure`, `ETTGame.tapeImpl_apply`). -/
theorem exists_simulate_tape_eq_pure (V : ℕ → ZMod (G.group κ d).order) {α : Type}
    (c : OracleComp (bitSpec (fun i => (qLen G ℓ i).eval κ) (fun i => (aLen G ℓ i).eval κ)) α)
    (st : BB1SimState G ℓ κ d × ℕ) :
    ∃ a st', simulate (ETTGame.tapeImpl (drawStep G ℓ b κ d g X Y Z T) V) c st =
      .pure (a, st') := by
  induction c generalizing st with
  | pure a => exact ⟨a, st, simulate_pure _ a st⟩
  | query i x k ih =>
    obtain ⟨y, s', h⟩ := exists_drawStep_eq_pure G ℓ b κ d g X Y Z T i x st.1 (V st.2)
    obtain ⟨a, st', hk⟩ := ih y (s', st.2 + 1)
    refine ⟨a, st', ?_⟩
    rw [simulate_query, ETTGame.tapeImpl_apply, h, OracleComp.pure_bind, OracleComp.pure_bind]
    exact hk

end Cases

/-! ### Drawn against ideal exponents -/

/-- A function with values `0` and `1` averages to the probability of the value `1`:
`𝔼_{x ← α} Φ x = Pr_{x ← α}[Φ x = 1]` (`prob_sample_eq_uprob`). -/
private theorem expect_sample_eq_uprob {α : Type} [Fintype α] [Nonempty α] (Φ : α → ℝ)
    (hΦ : ∀ x, Φ x = 0 ∨ Φ x = 1) :
    ProbComp.expect (ProbComp.sample α) Φ = uprob fun x => Φ x = 1 := by
  classical
  have h : Φ = fun x => if Φ x = 1 then 1 else 0 := by
    funext x
    rcases hΦ x with h0 | h1
    · rw [h0, if_neg zero_ne_one]
    · rw [h1, if_pos rfl]
  rw [← Bridge.prob_sample_eq_uprob, ProbComp.prob_eq_expect]
  conv_lhs => rw [h]

/-- **Drawn exponents against ideal ones, on a test with values `0` and `1`**: for `cap`
exponents and any `Φ` with values in `{0, 1}`,
`|𝔼_{T} Φ(draw ∘ T) − 𝔼_{U ← Z_p^cap} Φ(U)| ≤ cap · (1/2)^n`, `T` uniform over `cap` blocks of
`n · n` coins.

**Proof sketch.** Both averages are probabilities of the event `Φ = 1`
(`prob_sample_eq_uprob`); `cap` independent draws are `cap · (1/2)^n`-close to `cap` uniform
exponents (`statClose_draw`, `OneWay.statClose_pi`), and the event is a test set. -/
theorem abs_expect_draws_sub_le (κ : ℕ) (d : List Bool) (cap : ℕ)
    (Φ : (Fin cap → ZMod (G.group κ d).order) → ℝ) (hΦ : ∀ U, Φ U = 0 ∨ Φ U = 1) :
    |ProbComp.expect
        (ProbComp.sample (Fin cap → Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool))
        (fun T => Φ fun j => draw G κ d (T j)) -
      ProbComp.expect (ProbComp.sample (Fin cap → ZMod (G.group κ d).order)) Φ| ≤
      cap * (1 / 2 : ℝ) ^ (blockLen G).eval κ := by
  rw [expect_sample_eq_uprob _ fun T => hΦ _, expect_sample_eq_uprob Φ hΦ]
  exact (OneWay.statClose_pi (statClose_draw G κ d) cap).abs_uprob_sub_le fun U => Φ U = 1

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
