/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pairing.Assumptions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Joux's one-round tripartite Diffie–Hellman

[Jou00, §3]: three participants `A`, `B`, `C` share a group with a pairing and a public point.
Each picks a random exponent (`a`, `b`, `c`), broadcasts the multiple of the point once (one round,
`P_A = aP`, `P_B = bP`, `P_C = cP`), and computes the common key with
`F(x, P, Q) = e(P, Q)^x`: `K = F(a, P_B, P_C) = F(b, P_A, P_C) = F(c, P_A, P_B) = F(1, P, P)^{abc}`
[Jou00, p. 388]. In multiplicative notation, with the generator `g`: the messages are `g^a`,
`g^b`, `g^c`, and each key is `e(g^b, g^c)^a = e(g^a, g^c)^b = e(g^a, g^b)^c = e(g, g)^{abc}`.

**The single-point form.** [Jou00, §3] notes that with the Weil pairing on one point
`e_n(P, P) = 1`, so the key would be constant, and therefore uses two independent points `P`, `Q`
and the Tate pairing. In a symmetric bilinear group as defined in [BB04, §2.2], non-degeneracy is
`e(g, g) ≠ 1`, so the paper's first formula `F_W(x, P, Q) = e(P, Q)^x` already gives a
non-constant key, and one point suffices. This file formalizes that single-point form over the
abstract groups of `Pairing.BilinearGroup`.

**Security.** [Jou00, §5] gives no theorem; it says that "some Diffie–Hellman like problem and
Diffie–Hellman like decision problem should be hard in order to get security". The key
indistinguishability theorem here takes that decision problem to be Decision BDH [BB04, §3.1]:
an eavesdropper who sees the public point and the three broadcasts cannot tell the common key
from a uniform element of `G_T`.

**Deviation:** abstract symmetric bilinear groups (no curve, no Weil or Tate pairing); one public
point instead of two; multiplicative notation; the public point `g` is uniform in `G^*` (the
paper fixes "some point `P`"), the distribution under which [BB04, §3.1] states Decision BDH;
exponents in `Z_p`; security is the maintainer's formalization of [Jou00, §5]'s remark.

## Main definitions

* `TCSlib.Cryptography.KeyExchange.jouxMsg` — a participant's broadcast `g^x`.
* `TCSlib.Cryptography.KeyExchange.jouxKey` — the key `F(x, X, Y) = e(X, Y)^x`.
* `jouxGame`, `jouxAdv`, `JouxKeyIndist` — key indistinguishability for an eavesdropper.

## Main results

* `TCSlib.Cryptography.KeyExchange.jouxKey_eq` — every participant's key is `e(g, g)^{abc}`.
* `TCSlib.Cryptography.KeyExchange.joux_correct` — the three participants agree.
* `TCSlib.Cryptography.KeyExchange.jouxGame_eq_dbdhGame` — the eavesdropper's experiments are
  Decision BDH experiments.
* `TCSlib.Cryptography.KeyExchange.jouxKeyIndist_of_dbdhAssumption` — key indistinguishability
  under Decision BDH.

## References

* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000. §3 (pp. 387–388): the protocol and `F_W`; §5 (pp. 391–392):
  security issues.
* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §2.2 (bilinear groups), §3.1
  (Decision BDH).
-/

namespace TCSlib.Cryptography.KeyExchange

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

variable {wG wT : ℕ} (B : BilinearGroup wG wT)

/-- **A participant's broadcast** [Jou00, §3, `P_A = aP`]: the power `g^x` of the public
generator `g` by the participant's secret exponent `x ∈ Z_p`. -/
def jouxMsg (g : B.G) (x : ZMod B.order) : B.G := g ^ x.val

/-- `jouxMsg B g x = g ^ x.val`. -/
theorem jouxMsg_eq (g : B.G) (x : ZMod B.order) : jouxMsg B g x = g ^ x.val := rfl

/-- **A participant's key** [Jou00, §3, `F_W(x, P, Q) = e_n(P, Q)^x`]: from its secret exponent
`x` and the two other broadcasts `X`, `Y`, the key `e(X, Y)^x`. Participant `A` computes
`jouxKey B a P_B P_C`, `B` computes `jouxKey B b P_A P_C`, `C` computes `jouxKey B c P_A P_B`. -/
def jouxKey (x : ZMod B.order) (X Y : B.G) : B.GT := B.pair X Y ^ x.val

/-- `jouxKey B x X Y = e(X, Y) ^ x.val`. -/
theorem jouxKey_eq_pow (x : ZMod B.order) (X Y : B.G) : jouxKey B x X Y = B.pair X Y ^ x.val :=
  rfl

/-- Exponents of `G_T` multiply through `Z_p`: `u^{(abc mod p)} = u^{a b c}` with the
representatives `a.val, b.val, c.val`. -/
theorem pow_val_mul_mul (u : B.GT) (a b c : ZMod B.order) :
    u ^ (a * b * c).val = u ^ (a.val * b.val * c.val) := by
  rw [B.pow_val_mul_GT, pow_mul, B.pow_val_mul_GT, ← pow_mul]

/-- **The common key** [Jou00, p. 388, `F_W(a, P_B, P_C) = F_W(1, P, P)^{abc}`]: participant `A`'s
key `e(g^b, g^c)^a` is `e(g, g)^{abc}`. -/
theorem jouxKey_eq (g : B.G) (a b c : ZMod B.order) :
    jouxKey B a (jouxMsg B g b) (jouxMsg B g c) = B.pair g g ^ (a * b * c).val := by
  rw [jouxKey_eq_pow, jouxMsg_eq, jouxMsg_eq, B.bilinear_pow, pow_val_mul_mul, ← pow_mul]
  congr 1
  ring

/-- **Correctness: the three participants agree** [Jou00, p. 388,
`F_W(a, P_B, P_C) = F_W(b, P_A, P_C) = F_W(c, P_A, P_B)`]: `e(g^b, g^c)^a = e(g^a, g^c)^b` and
`e(g^a, g^c)^b = e(g^a, g^b)^c`. -/
theorem joux_correct (g : B.G) (a b c : ZMod B.order) :
    jouxKey B a (jouxMsg B g b) (jouxMsg B g c) = jouxKey B b (jouxMsg B g a) (jouxMsg B g c) ∧
      jouxKey B b (jouxMsg B g a) (jouxMsg B g c) =
        jouxKey B c (jouxMsg B g a) (jouxMsg B g b) := by
  refine ⟨?_, ?_⟩ <;> rw [jouxKey_eq, jouxKey_eq] <;> congr 2 <;> ring

/-- **The key-indistinguishability experiment** for the eavesdropper `A` at parameter `κ`: draw
the generator's coins `r` (group `B`, description `d`), the public generator `g ∈ G^*`, the
secret exponents `a, b, c ∈ Z_p`, a uniform `K ∈ G_T` and `A`'s coins `ρ`; give `A` the
description, the public generator, the three broadcasts and either the common key
`e(g^b, g^c)^a` (`real`) or `K`, in the string format of Decision BDH (`tupleStr`). -/
noncomputable def jouxGame (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
  (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
  (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
    ZMod (G.inst κ r).order)).bind fun abc =>
  (ProbComp.sample (G.inst κ r).GT).bind fun K =>
  (ProbComp.sample (A.Coins κ)).bind fun ρ =>
    .pure (A.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1
      (jouxMsg (G.inst κ r) g.1 abc.1) (jouxMsg (G.inst κ r) g.1 abc.2.1)
      (jouxMsg (G.inst κ r) g.1 abc.2.2)
      (if real then jouxKey (G.inst κ r) abc.1 (jouxMsg (G.inst κ r) g.1 abc.2.1)
        (jouxMsg (G.inst κ r) g.1 abc.2.2) else K)) ρ)

/-- The key-indistinguishability experiment draws the generator's coins, `g ∈ G^*`,
`(a, b, c) ∈ Z_p³`, `K ∈ G_T` and the eavesdropper's coins, and runs the eavesdropper on the
transcript `g, g^a, g^b, g^c` with `A`'s key if `real` and `K` otherwise. -/
theorem jouxGame_eq (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) :
    jouxGame G A real κ =
      (ProbComp.sample (G.gen.Coins κ)).bind fun r =>
      (ProbComp.sample {x : (G.inst κ r).G // x ≠ 1}).bind fun g =>
      (ProbComp.sample (ZMod (G.inst κ r).order × ZMod (G.inst κ r).order ×
        ZMod (G.inst κ r).order)).bind fun abc =>
      (ProbComp.sample (G.inst κ r).GT).bind fun K =>
      (ProbComp.sample (A.Coins κ)).bind fun ρ =>
        .pure (A.distinguisherL κ (tupleStr (G.inst κ r) (G.desc κ r) g.1
          (jouxMsg (G.inst κ r) g.1 abc.1) (jouxMsg (G.inst κ r) g.1 abc.2.1)
          (jouxMsg (G.inst κ r) g.1 abc.2.2)
          (if real then jouxKey (G.inst κ r) abc.1 (jouxMsg (G.inst κ r) g.1 abc.2.1)
            (jouxMsg (G.inst κ r) g.1 abc.2.2) else K)) ρ) :=
  rfl

/-- **Each key-indistinguishability experiment is a Decision BDH experiment**: with the key
`e(g^b, g^c)^a = e(g, g)^{abc}` (`jouxKey_eq`) the transcript and key are drawn from `P_BDH`, and
with a uniform `K` from `R_BDH`, in the same string format, so
`jouxGame G A real κ = G.dbdhGame A real κ`. -/
theorem jouxGame_eq_dbdhGame (G : BilinearGen) (A : NUPPT) (real : Bool) (κ : ℕ) :
    jouxGame G A real κ = G.dbdhGame A real κ := by
  rw [jouxGame_eq, BilinearGen.dbdhGame_eq]
  simp only [jouxKey_eq]
  rfl

/-- **The eavesdropper's advantage** at `κ`: `|Pr[A(transcript, K) = 1] − Pr[A(transcript,
key) = 1]|`. -/
noncomputable def jouxAdv (G : BilinearGen) (A : NUPPT) (κ : ℕ) : ℝ :=
  advantage (jouxGame G A false κ) (jouxGame G A true κ)

/-- `jouxAdv G A κ = advantage (jouxGame G A false κ) (jouxGame G A true κ)`. -/
theorem jouxAdv_eq (G : BilinearGen) (A : NUPPT) (κ : ℕ) :
    jouxAdv G A κ = advantage (jouxGame G A false κ) (jouxGame G A true κ) := rfl

/-- **Key indistinguishability of Joux's protocol** relative to the generator `G`: every
non-uniform PPT eavesdropper has negligible advantage in telling the common key from a uniform
element of `G_T`, given the public generator and the three broadcasts. The security goal of
[Jou00, §3] ("this common value `K_{A,B,C}` will be hard to compute given `P_A`, `P_B` and `P_C`"),
in its decisional form [Jou00, §5]. -/
def JouxKeyIndist (G : BilinearGen) : Prop := ∀ A : NUPPT, Negligible fun κ => jouxAdv G A κ

/-- `JouxKeyIndist G` iff `κ ↦ jouxAdv G A κ` is negligible for every non-uniform PPT `A`. -/
theorem jouxKeyIndist_iff (G : BilinearGen) :
    JouxKeyIndist G ↔ ∀ A : NUPPT, Negligible fun κ => jouxAdv G A κ := Iff.rfl

/-- **Joux's protocol has indistinguishable keys under Decision BDH** ([Jou00, §5] with the
decision problem of [BB04, §3.1]).

**Source:** [Jou00] states no theorem; this is the formal version of its §5 requirement
(module docstring).

The eavesdropper is itself the Decision BDH distinguisher: `jouxAdv G A κ = G.dbdhAdv A κ`
(`jouxGame_eq_dbdhGame`). -/
theorem jouxKeyIndist_of_dbdhAssumption (G : BilinearGen) (h : G.DBDHAssumption) :
    JouxKeyIndist G := by
  intro A
  have hfun : (fun κ => jouxAdv G A κ) = fun κ => G.dbdhAdv A κ := funext fun κ => by
    rw [jouxAdv_eq, BilinearGen.dbdhAdv_eq, jouxGame_eq_dbdhGame, jouxGame_eq_dbdhGame]
  rw [hfun]
  exact G.dbdhAssumption_iff.1 h A

end TCSlib.Cryptography.KeyExchange
