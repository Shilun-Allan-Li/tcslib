/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.ZeroKnowledge.Defs
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Real and normalized phase-prefix folds

## Main definitions

* `realStep`, `simStep`: append a real or normalized phase and its empty prover fillers.
* `realPrefix`, `simPrefix`: semantic folds on independent typed phase coins.

These definitions directly use the public core `Fin.foldl` combinator. They specify finite
samplers; they introduce no machine or control host. The strict-PPT simulator is supplied by
`SimulatorMachine`, using the previously published counted-loop host.

## Main results

* The `_eq` readers publish each step and fold formula.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential composition).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4 (sequential composition).
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- For `π,V,x,y,z,rV,p,i,pre,rP`, append to `pre` the real verifier-received messages of
`π.P` against `phaseVerifier V` at `phaseAux z rV i pre` on tapes `List.ofFn rP, []`, then
`π.rounds.eval |x| - p` empty prover fillers. [PS10, Theorem 175.1].
`realStep π V x y z rV p i pre rP = pre ++ ((exec π.P (phaseVerifier V) π.verifierFirst x y
(phaseAux z rV i pre) (List.ofFn rP) [] (π.rounds.eval x.length)).2 ++ List.replicate (π.rounds.eval
x.length - p) [])`. -/
def realStep (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p i : ℕ)
    (pre : List (List Bool)) (rP : π.P.Coins x.length) : List (List Bool) :=
  pre ++ ((exec π.P (phaseVerifier V) π.verifierFirst x y (phaseAux z rV i pre)
    (List.ofFn rP) [] (π.rounds.eval x.length)).2 ++
      List.replicate (π.rounds.eval x.length - p) [])

/-- `realStep π V x y z rV p i pre rP` is `pre` followed by the original real phase's
received messages on `(List.ofFn rP, [])`, then `k-p` empty fillers, for `k=π.rounds.eval |x|`.
-/
theorem realStep_eq (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p i : ℕ)
    (pre : List (List Bool)) (rP : π.P.Coins x.length) :
    realStep π V x y z rV p i pre rP =
      pre ++ ((exec π.P (phaseVerifier V) π.verifierFirst x y (phaseAux z rV i pre)
        (List.ofFn rP) [] (π.rounds.eval x.length)).2 ++
          List.replicate (π.rounds.eval x.length - p) []) := rfl

/-- For `S,x,z,rV,k,B,p,i,pre,rS`, append the `p` normalized `B`-bounded messages decoded
from `S.simulate x (phaseAux z rV i pre) rS`, followed by `k-p` empty fillers.
[PS10, Theorem 175.1; Gol01, §4.3.4].
`simStep S x z rV k B p i pre rS = pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
(S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) [])`. -/
def simStep (S : NUPPT) (x z rV : List Bool) (k B p i : ℕ)
    (pre : List (List Bool)) (rS : S.Coins x.length) : List (List Bool) :=
  pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
    (S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) [])

/-- `simStep S x z rV k B p i pre rS` appends the normalized phase result and `k-p` empty
fillers to `pre`, using auxiliary word `phaseAux z rV i pre`.
`simStep S x z rV k B p i pre rS = pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
(S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) [])`. -/
theorem simStep_eq (S : NUPPT) (x z rV : List Bool) (k B p i : ℕ)
    (pre : List (List Bool)) (rS : S.Coins x.length) :
    simStep S x z rV k B p i pre rS =
      pre ++ (normalizePhaseMsgs x (phaseAux z rV i pre) p B
        (S.simulate x (phaseAux z rV i pre) rS) ++ List.replicate (k - p) []) := rfl

/-- `realPrefix π V x y z rV p q r` folds the `q` real phase steps, starting with `[]` and
using `r i` in phase `i`. [PS10, Theorem 175.1].
`realPrefix π V x y z rV p q r = Fin.foldl q (fun pre i => realStep π V x y z rV p i pre (r i))
[]`. -/
def realPrefix (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
    (r : Fin q → π.P.Coins x.length) : List (List Bool) :=
  Fin.foldl q (fun pre i => realStep π V x y z rV p i pre (r i)) []

/-- `realPrefix π V x y z rV p q r = Fin.foldl q (fun pre i => realStep … i pre (r i)) []`.
-/
theorem realPrefix_eq (π : Protocol) (V : Strategy) (x y z rV : List Bool) (p q : ℕ)
    (r : Fin q → π.P.Coins x.length) :
    realPrefix π V x y z rV p q r =
      Fin.foldl q (fun pre i => realStep π V x y z rV p i pre (r i)) [] := rfl

/-- `simPrefix S x z rV k B p q r` folds the `q` normalized phase steps from `[]`, using
`r i` in phase `i`. [PS10, Theorem 175.1; Gol01, §4.3.4].
`simPrefix S x z rV k B p q r = Fin.foldl q (fun pre i => simStep S x z rV k B p i pre (r i))
[]`. -/
def simPrefix (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
    (r : Fin q → S.Coins x.length) : List (List Bool) :=
  Fin.foldl q (fun pre i => simStep S x z rV k B p i pre (r i)) []

/-- `simPrefix S x z rV k B p q r = Fin.foldl q (fun pre i => simStep … i pre (r i)) []`.
-/
theorem simPrefix_eq (S : NUPPT) (x z rV : List Bool) (k B p q : ℕ)
    (r : Fin q → S.Coins x.length) :
    simPrefix S x z rV k B p q r =
      Fin.foldl q (fun pre i => simStep S x z rV k B p i pre (r i)) [] := rfl

end TCSlib.Cryptography.SequentialZK
