/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.UniversalLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Realisation of reduction functions by non-uniform machines

A security reduction in the iO-components campaign is written as a Lean function
`R : ∀ m, X m → List Bool → List Bool` of the parameter `m`, the assumption's typed challenge
`x : X m` and a coin string `r`. Its advice, chosen by the security proof (the averaging choice
`ω*`), is fixed inside `R` by partial application. `Complexity.NUPPT.RealizesOn B enc c R` says
that the non-uniform machine `B` [PS10, Definition 26.8] computes `R` on the **encoded**
challenges: `B` has coin polynomial `c`, and at every parameter `m`, on the string `enc m x`
that the assumption's game hands its distinguisher, with any coin string of the layout's length
`c.eval m`, `B` outputs `R m x r`.

The predicate constrains `B` on nothing else: not on strings that are not encodings, not on coin
strings of another length, and not on its advice. `B`'s own `advice` field is never read back;
the reduction's advice lives in `R`. This is what the reductions' later machine constructions
deliver: programs that are correct on well-formed inputs only.

The intended use, in both iO-component jobs [JLS26, proof of Proposition 4.1;
GJLS21, Definition 4.3 and its reductions], is the statement form "there is advice `ω*` such
that **every** NUPPT realising the reductions at `ω*` satisfies the explicit inequality". The
reduction functions have the shape
`XRed A ω m x r := A.runAtL (φ m) (XPre m (ω m) x) (r.take (A.coinLen (φ m)))`, a
deterministic pre-processing of the challenge followed by one activation of the adversary `A` at
the parameter `φ m` on the first `A.coinLen (φ m)` coins. That is the conclusion shape of
`Complexity.NUPPT.exists_reparam_pre_post` with `post := id`, so a polynomial-time map that
agrees with the pre-processing on encodings yields a realiser
(`Complexity.NUPPT.exists_realizesOn_of_preTarget`).

**Uniformity.** This predicate is for reductions, which may use advice: a realiser is a
non-uniform PPT, and the reduction's advice `ω*` need not be computable. Honest algorithms
(key generation, evaluation, samplers, simulators) never use it. Their efficiency is
`Complexity.PolyTimeComputable` of an explicit map, or `∃ A, A.Uniform ∧ A.Computes f`.

## Main definitions

* `Complexity.NUPPT.RealizesOn B enc c R`: `B.coins = c` and, for every parameter `m`,
  challenge `x` and coin string `r` of length `c.eval m`, `B.runAtL m (enc m x) r = R m x r`.

## Main results

* `Complexity.NUPPT.realizesOn_iff`, `RealizesOn.coins_eq`, `RealizesOn.runAtL_eq` — the reader.
* `RealizesOn.runAt_eq`, `RealizesOn.distinguisherL_eq`,
  `RealizesOn.runAt_coinsEquivPoly_symm` — typed coins: the realiser's output, and its verdict as
  a distinguisher, on an encoded challenge are the reduction function's.
* `realizesOn_of_forall`, `RealizesOn.congr` — introduction from agreement on every coin string,
  and change of the reduction function along agreement on the layout's coin strings.
* `exists_realizesOn_reparam_pre_post`, `exists_realizesOn_of_preTarget`,
  `exists_realizesOn_of_preTarget_id` — the link "polynomial-time pre-processing target ⇒
  realiser" through `exists_reparam_pre_post`, for an arbitrary parameter map and for the
  identity.
* `realizesOn_self`, `realizesOn_self_take` — non-vacuity: every machine realises its own
  activation on any encoding, and the identity reduction in the reduction shape.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8: non-uniform probabilistic polynomial-time machines.)
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, 2026. (Context: the reductions of the proof of
  Proposition 4.1, against non-uniform adversaries.)
* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version Cryptology ePrint Archive 2020/764. (Context: Definition 4.3 and
  the reductions to DLIN.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ## The predicate and its readers -/

/-- **`B` realises the reduction function `R` on the encoded challenges `enc`, with coin
polynomial `c`**: `B.coins = c` and, at every parameter `m`, for every challenge `x : X m` and
every coin string `r` of length `c.eval m`, `B.runAtL m (enc m x) r = R m x r`.

The machine is a non-uniform PPT [PS10, Definition 26.8]. Only encoded challenges and coin
strings of the layout's length are constrained, and `B`'s advice is not read back: the
reduction's advice is fixed inside `R`. This is a predicate for **reductions**. Honest
algorithms use `PolyTimeComputable` or `∃ A, A.Uniform ∧ A.Computes f`, never this.
Glue: the realisation step that [JLS26, proof of Proposition 4.1] and
[GJLS21, Definition 4.3]'s reductions leave implicit, with the reductions written as Lean
functions of challenge and coins. -/
def _root_.Complexity.NUPPT.RealizesOn (B : NUPPT) {X : ℕ → Type*} (enc : ∀ m, X m → List Bool)
    (c : PolyExpr) (R : ∀ m, X m → List Bool → List Bool) : Prop :=
  B.coins = c ∧ ∀ m (x : X m) (r : List Bool), r.length = c.eval m →
    B.runAtL m (enc m x) r = R m x r

/-- The defining property of `RealizesOn`: `B.RealizesOn enc c R ↔ B.coins = c ∧
∀ m x r, |r| = c(m) → B.runAtL m (enc m x) r = R m x r`. -/
theorem _root_.Complexity.NUPPT.realizesOn_iff (B : NUPPT) {X : ℕ → Type*}
    (enc : ∀ m, X m → List Bool) (c : PolyExpr) (R : ∀ m, X m → List Bool → List Bool) :
    B.RealizesOn enc c R ↔ B.coins = c ∧ ∀ m (x : X m) (r : List Bool), r.length = c.eval m →
      B.runAtL m (enc m x) r = R m x r :=
  Iff.rfl

variable {B : NUPPT} {X : ℕ → Type*} {enc : ∀ m, X m → List Bool} {c : PolyExpr}
  {R : ∀ m, X m → List Bool → List Bool}

/-- A realiser has the stated coin polynomial: `B.coins = c`. -/
theorem _root_.Complexity.NUPPT.RealizesOn.coins_eq (h : B.RealizesOn enc c R) : B.coins = c :=
  h.1

/-- A realiser's untyped activation on an encoded challenge, with a coin string of length
`c(m)`, is the reduction function: `B.runAtL m (enc m x) r = R m x r`. -/
theorem _root_.Complexity.NUPPT.RealizesOn.runAtL_eq (h : B.RealizesOn enc c R) (m : ℕ)
    (x : X m) {r : List Bool} (hr : r.length = c.eval m) : B.runAtL m (enc m x) r = R m x r :=
  h.2 m x r hr

/-- A realiser's typed activation on an encoded challenge is the reduction function on the
coin list: `B.runAt m (enc m x) ρ = R m x (List.ofFn ρ)` for `ρ : B.Coins m`. -/
theorem _root_.Complexity.NUPPT.RealizesOn.runAt_eq (h : B.RealizesOn enc c R) (m : ℕ) (x : X m)
    (ρ : B.Coins m) : B.runAt m (enc m x) ρ = R m x (List.ofFn ρ) := by
  rw [NUPPT.runAt_eq]
  exact h.runAtL_eq m x (by rw [B.length_ofFn_coins, h.coins_eq])

/-- **The verdict lemma**: a realiser's verdict as a distinguisher on an encoded challenge is the
reduction function's, `B.distinguisherL m (enc m x) ρ = decide (R m x (List.ofFn ρ) = [true])`
(`NUPPT.distinguisherL_eq`, `RealizesOn.runAt_eq`). -/
theorem _root_.Complexity.NUPPT.RealizesOn.distinguisherL_eq (h : B.RealizesOn enc c R) (m : ℕ)
    (x : X m) (ρ : B.Coins m) :
    B.distinguisherL m (enc m x) ρ = decide (R m x (List.ofFn ρ) = [true]) := by
  rw [NUPPT.distinguisherL_eq, h.runAt_eq]

/-- A realiser's activation on coins carried from bit strings of the coin polynomial's length:
`B.runAt m (enc m x) ((coinsEquivPoly h.coins_eq m).symm w) = R m x (List.ofFn w)` for
`w : Fin (c.eval m) → Bool`. Glue: moves a consumer's sums over `B.Coins m` to sums over
`{0,1}^{c(m)}`, where the reduction function lives. -/
theorem _root_.Complexity.NUPPT.RealizesOn.runAt_coinsEquivPoly_symm (h : B.RealizesOn enc c R)
    (m : ℕ) (x : X m) (w : Fin (c.eval m) → Bool) :
    B.runAt m (enc m x) ((NUPPT.coinsEquivPoly h.coins_eq m).symm w) = R m x (List.ofFn w) := by
  rw [h.runAt_eq, NUPPT.coinsEquivPoly_symm_ofFn]

/-- **Introduction from agreement on every coin string**: if `B.coins = c` and
`B.runAtL m (enc m x) r = R m x r` for every coin string `r` (the form of
`exists_reparam_pre_post`'s conclusion), then `B` realises `R`. -/
theorem _root_.Complexity.NUPPT.realizesOn_of_forall (hc : B.coins = c)
    (h : ∀ m (x : X m) (r : List Bool), B.runAtL m (enc m x) r = R m x r) :
    B.RealizesOn enc c R :=
  ⟨hc, fun m x r _ => h m x r⟩

/-- **Changing the reduction function**: a realiser of `R` realises every `R'` that agrees with
`R` on the coin strings of length `c(m)`. Glue: matches a construction's conclusion with a
job's named reduction function. -/
theorem _root_.Complexity.NUPPT.RealizesOn.congr {R' : ∀ m, X m → List Bool → List Bool}
    (h : B.RealizesOn enc c R)
    (hR : ∀ m (x : X m) (r : List Bool), r.length = c.eval m → R m x r = R' m x r) :
    B.RealizesOn enc c R' :=
  ⟨h.coins_eq, fun m x r hr => (h.runAtL_eq m x hr).trans (hR m x r hr)⟩

/-! ## Non-vacuity -/

/-- **Every machine realises its own activation**: `A.RealizesOn enc A.coins
(fun m x r => A.runAtL m (enc m x) r)`, for any encoding. Glue: the predicate is satisfiable. -/
theorem _root_.Complexity.NUPPT.realizesOn_self (A : NUPPT) (enc : ∀ m, X m → List Bool) :
    A.RealizesOn enc A.coins (fun m x r => A.runAtL m (enc m x) r) :=
  NUPPT.realizesOn_of_forall rfl fun _ _ _ => rfl

/-- **The identity reduction is realised by the adversary itself**: with pre-processing the
encoding (`XPre m ω x := enc m x`) and `φ := id`, the reduction function
`fun m x r => A.runAtL m (enc m x) (r.take (A.coinLen m))` is realised by `A` with coins
`A.coins`. Glue: the reduction shape is satisfiable without any construction, because only
coin strings of the layout's length are constrained.

**Proof sketch.** A coin string of length `A.coins(m) = A.coinLen m` is its own prefix of that
length. -/
theorem _root_.Complexity.NUPPT.realizesOn_self_take (A : NUPPT) (enc : ∀ m, X m → List Bool) :
    A.RealizesOn enc A.coins (fun m x r => A.runAtL m (enc m x) (r.take (A.coinLen m))) :=
  ⟨rfl, fun m x r hr => by
    beta_reduce
    rw [List.take_of_length_le (by rw [hr, NUPPT.coinLen_eq])]⟩

/-! ## The link to polynomial-time pre-processing -/

/-- **Realisers from polynomial-time pre- and post-processing** (string form): for an `NUPPT`
`A`, a parameter map `φ` majorised by the syntactic polynomial `p`, an advice family `β m` of
length `≤ b(m)`, and polynomial-time `pre`, `post` with
`pre ⟨β m, enc m x⟩ = g m x` on the encoded challenges, some `NUPPT` realises
`fun m x r => post (A.runAtL (φ m) (g m x) (r.take (A.coinLen (φ m))))` on `enc` with coins
`A.coins.subst p`. Glue: `Complexity.NUPPT.exists_reparam_pre_post` restated in the predicate's
vocabulary ([PS10, §2.1, implicit]).

**Proof sketch.** `exists_reparam_pre_post` gives `B` with coins `A.coins.subst p` and
`B.runAtL m y r = post (A.runAtL (φ m) (pre ⟨β m, y⟩) (r.take (A.coinLen (φ m))))` for every
`y` and `r`; at `y := enc m x` rewrite `pre ⟨β m, enc m x⟩ = g m x`. -/
theorem _root_.Complexity.NUPPT.exists_realizesOn_reparam_pre_post (A : NUPPT) (φ : ℕ → ℕ)
    (p : PolyExpr) (hφ : ∀ m, φ m ≤ p.eval m) (enc : ∀ m, X m → List Bool) (β : ℕ → List Bool)
    (b : PolyExpr) (hβ : ∀ m, (β m).length ≤ b.eval m) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post)
    (g : ∀ m, X m → List Bool) (hg : ∀ m (x : X m), pre (pairEncode (β m) (enc m x)) = g m x) :
    ∃ B : NUPPT, B.RealizesOn enc (A.coins.subst p)
      (fun m x r => post (A.runAtL (φ m) (g m x) (r.take (A.coinLen (φ m))))) := by
  obtain ⟨B, hc, hB⟩ := NUPPT.exists_reparam_pre_post A φ p hφ β b hβ hpre hpost
  exact ⟨B, NUPPT.realizesOn_of_forall hc fun m x r => by rw [hB, hg]⟩

/-- **Targets ⇒ realisers** (typed form, the link of the sPRG job's Q-S11 (A)): let `Ω m` be the
reduction's advice type with encoding `encΩ`, `pre m w x` its pre-processing, and `f` a
polynomial-time map with `f ⟨encΩ m w, enc m x⟩ = pre m w x` for all advice `w` and challenges
`x` (the pre-processing target). Then for every advice family `ω` whose encodings have length
`≤ b(m)`, some `NUPPT` realises the reduction function
`fun m x r => A.runAtL (φ m) (pre m (ω m) x) (r.take (A.coinLen (φ m)))` on `enc` with coins
`A.coins.subst p`, for every parameter map `φ ≤ p`. Glue: the step "targets ⇒ realisers ⇒
∃ NUPPT" with which the reductions of [JLS26, proof of Proposition 4.1] become machines.

**Proof sketch.** `exists_realizesOn_reparam_pre_post` with `β m := encΩ m (ω m)`,
`pre := f`, `post := id` and `g m x := pre m (ω m) x`; the target's equation at `w := ω m` is
the agreement hypothesis, and `id` is polynomial-time. -/
theorem _root_.Complexity.NUPPT.exists_realizesOn_of_preTarget (A : NUPPT) (φ : ℕ → ℕ)
    (p : PolyExpr) (hφ : ∀ m, φ m ≤ p.eval m) {Ω : ℕ → Type*} (enc : ∀ m, X m → List Bool)
    (encΩ : ∀ m, Ω m → List Bool) (pre : ∀ m, Ω m → X m → List Bool)
    {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hfpre : ∀ m (w : Ω m) (x : X m), f (pairEncode (encΩ m w) (enc m x)) = pre m w x)
    (ω : ∀ m, Ω m) (b : PolyExpr) (hb : ∀ m, (encΩ m (ω m)).length ≤ b.eval m) :
    ∃ B : NUPPT, B.RealizesOn enc (A.coins.subst p)
      (fun m x r => A.runAtL (φ m) (pre m (ω m) x) (r.take (A.coinLen (φ m)))) :=
  NUPPT.exists_realizesOn_reparam_pre_post A φ p hφ enc (fun m => encΩ m (ω m)) b hb hf
    polyTimeComputable_id (fun m x => pre m (ω m) x) fun m x => hfpre m (ω m) x

/-- **Targets ⇒ realisers at the adversary's own parameter** (`φ := id`, the PHFE job's
reduction shape): under the hypotheses of `exists_realizesOn_of_preTarget`, some `NUPPT`
realises `fun m x r => A.runAtL m (pre m (ω m) x) (r.take (A.coinLen m))` on `enc` with the
adversary's own coin polynomial `A.coins`. Glue: specialisation of
`exists_realizesOn_of_preTarget`.

**Proof sketch.** Take `φ := id` and `p := var` (`eval_var`), and rewrite
`A.coins.subst var = A.coins` (`PolyExpr.subst_var`). -/
theorem _root_.Complexity.NUPPT.exists_realizesOn_of_preTarget_id (A : NUPPT) {Ω : ℕ → Type*}
    (enc : ∀ m, X m → List Bool) (encΩ : ∀ m, Ω m → List Bool)
    (pre : ∀ m, Ω m → X m → List Bool) {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hfpre : ∀ m (w : Ω m) (x : X m), f (pairEncode (encΩ m w) (enc m x)) = pre m w x)
    (ω : ∀ m, Ω m) (b : PolyExpr) (hb : ∀ m, (encΩ m (ω m)).length ≤ b.eval m) :
    ∃ B : NUPPT, B.RealizesOn enc A.coins
      (fun m x r => A.runAtL m (pre m (ω m) x) (r.take (A.coinLen m))) := by
  have h := NUPPT.exists_realizesOn_of_preTarget A id .var (fun m => (PolyExpr.eval_var m).ge)
    enc encΩ pre hf hfpre ω b hb
  rwa [PolyExpr.subst_var] at h

end TCSlib.Cryptography
