/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.PrefixFolds
import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Phase-fold equations and simulator endpoint

## Main definitions

This module introduces no definitions.

## Main results

* `realPrefix_zero`, `simPrefix_zero`: no phases give the empty history.
* `realPrefix_succ`, `simPrefix_succ`: the last coin extends the earlier prefix by one step.
* `realPrefix_snoc`, `simPrefix_snoc`: the corresponding independent-table snoc equations.

The fold equations directly reuse core `Fin.foldl_zero` and `Fin.foldl_succ_last`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential composition).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4 (sequential composition).
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For `π,V,x,y,z,rV,p,r`, `realPrefix π V x y z rV p 0 r = []`. -/
theorem realPrefix_zero (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p : ℕ)
    (r : Fin 0 → π.P.Coins x.length) : realPrefix π V x y z rV p 0 r = [] := by
  rw [realPrefix_eq, Fin.foldl_zero]

/-- For `π,V,x,y,z,rV,p,q,r`, the prefix on `q+1` coins equals `realStep` at index `q`
applied to the prefix on the first `q` coins and to the last coin `r (Fin.last q)`.
`realPrefix π V x y z rV p (q + 1) r = realStep π V x y z rV p q (realPrefix π V x y z rV p q (fun i
=> r i.castSucc)) (r (Fin.last q))`. -/
theorem realPrefix_succ (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
    (r : Fin (q + 1) → π.P.Coins x.length) :
    realPrefix π V x y z rV p (q + 1) r =
      realStep π V x y z rV p q
        (realPrefix π V x y z rV p q (fun i => r i.castSucc)) (r (Fin.last q)) := by
  rw [realPrefix_eq, Fin.foldl_succ_last, realPrefix_eq]
  rfl

/-- For `π,V,x,y,z,rV,p,q,r,coin`, appending `coin` to `r` extends its real prefix by
`realStep π V x y z rV p q` on that coin.
`realPrefix π V x y z rV p (q + 1) (Fin.snoc r coin) = realStep π V x y z rV p q (realPrefix π V x y
z rV p q r) coin`. -/
theorem realPrefix_snoc (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
    (r : Fin q → π.P.Coins x.length) (coin : π.P.Coins x.length) :
    realPrefix π V x y z rV p (q + 1) (Fin.snoc r coin) =
      realStep π V x y z rV p q (realPrefix π V x y z rV p q r) coin := by
  rw [realPrefix_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- For `S,x,z,rV,k,B,p,r`, `simPrefix S x z rV k B p 0 r = []`. -/
theorem simPrefix_zero (S : NUPPT) (x z rV : List Bool) (k B p : ℕ)
    (r : Fin 0 → S.Coins x.length) : simPrefix S x z rV k B p 0 r = [] := by
  rw [simPrefix_eq, Fin.foldl_zero]

/-- For `S,x,z,rV,k,B,p,q,r`, the prefix on `q+1` coins equals `simStep` at index `q`
applied to the prefix on the first `q` coins and to the last coin `r (Fin.last q)`.
`simPrefix S x z rV k B p (q + 1) r = simStep S x z rV k B p q (simPrefix S x z rV k B p q (fun i =>
r i.castSucc)) (r (Fin.last q))`. -/
theorem simPrefix_succ (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
    (r : Fin (q + 1) → S.Coins x.length) :
    simPrefix S x z rV k B p (q + 1) r =
      simStep S x z rV k B p q
        (simPrefix S x z rV k B p q (fun i => r i.castSucc)) (r (Fin.last q)) := by
  rw [simPrefix_eq, Fin.foldl_succ_last, simPrefix_eq]
  rfl

/-- For `S,x,z,rV,k,B,p,q,r,coin`, appending `coin` to `r` extends its normalized prefix by
`simStep S x z rV k B p q` on that coin.
`simPrefix S x z rV k B p (q + 1) (Fin.snoc r coin) = simStep S x z rV k B p q (simPrefix S x z rV k
B p q r) coin`. -/
theorem simPrefix_snoc (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
    (r : Fin q → S.Coins x.length) (coin : S.Coins x.length) :
    simPrefix S x z rV k B p (q + 1) (Fin.snoc r coin) =
      simStep S x z rV k B p q (simPrefix S x z rV k B p q r) coin := by
  rw [simPrefix_succ]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- For `S,k,B,verifierFirst,x,z,rV,rS,q,coins`, if every block `i<q` of `rS` is
`List.ofFn (coins i)`, the typed normalized fold equals the simulator prefix:
`simPrefix … q coins = phasePrefix S k B verifierFirst x z rV rS q`, using the numeric real
message count `if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`.
[PS10, Theorem 175.1; Gol01, §4.3.4].

**Proof sketch.** Induct on the phase count. Remove the last typed coin from the fold and
use the simulator's published phase reader on the corresponding raw coin block. The
induction hypothesis identifies the earlier prefixes; both final steps then normalize the
same simulator call and append the same empty fillers. -/
theorem simPrefix_eq_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (q : ℕ) (coins : Fin q → S.Coins x.length)
    (hcoins : ∀ i : Fin q, coinBlock (S.coinLen x.length) i rS = List.ofFn (coins i)) :
    simPrefix S x z rV (k.eval x.length) (B.eval x.length)
      (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) q coins =
        phasePrefix S k B verifierFirst x z rV rS q := by
  induction q with
  | zero => rw [simPrefix_zero, phasePrefix_zero]
  | succ q ih =>
    -- Restrict the typed table to its earlier coordinates.
    have hpre := ih (fun i : Fin q => coins i.castSucc) (fun i => by
      simpa only [Fin.coe_castSucc] using hcoins i.castSucc)
    have hlast : coinBlock (S.coinLen x.length) q rS =
        List.ofFn (coins (Fin.last q)) := by
      simpa only [Fin.val_last] using hcoins (Fin.last q)
    -- Both endpoint readers append the same last normalized phase.
    rw [simPrefix_succ, phasePrefix_succ_simulate S k B verifierFirst x z rV rS q
      (coins (Fin.last q)) hlast]
    dsimp only
    rw [hpre, simStep_eq]

end TCSlib.Cryptography.SequentialZK
