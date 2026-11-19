/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Simulator
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Committed two-stage adversaries

The first machine commits to both input parts and all function descriptions before public
parameters are drawn. The second machine receives the first machine's state and the public
view. A total fixed-window parser interprets arbitrary first-stage outputs, padding short
windows with false and leaving the remaining suffix as state.

## Main definitions

* `TwoStage`: the pair of non-uniform PPT machines.
* `Commitment`: both input parts, the ordered function list, and the retained state.
* `Commitment.decode`: the total parser of the first machine's output.

## Main results

Equation readers specify the parser and the allowed simulator information.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.3 and Remarks 4.3 and 4.6.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- A two-stage adversary is a pair of non-uniform PPT machines. The first commits before
public parameters, and the second distinguishes the resulting public view
[GJLS21, Definition 4.3, at epsilon one; Remark 4.6, many keys]. -/
structure TwoStage where
  /-- The commitment machine. -/
  first : NUPPT
  /-- The final distinguishing machine. -/
  second : NUPPT

/-- A commitment contains both inputs, the ordered function descriptions, and arbitrary
first-stage state [GJLS21, Definition 4.3]. The key count is the polynomial budget. -/
structure Commitment (C : FnClass) (q : PolyExpr) (κ : ℕ) where
  /-- The public challenge input. -/
  publicInput : Fin (C.pubLen.eval κ) → Bool
  /-- The private challenge input. -/
  privateInput : Fin (C.privLen.eval κ) → Bool
  /-- All committed function descriptions. -/
  functions : Fin (q.eval κ) → Fin (C.fnLen.eval κ) → Bool
  /-- The first machine's retained state. -/
  state : List Bool

namespace Commitment

variable {C : FnClass} {q : PolyExpr} {κ : ℕ}

/-- Decode successive public, private and function windows, followed by an arbitrary state
suffix. Missing input bits are false. This total parser imposes no validity restriction on
non-uniform adversaries [GJLS21, Definition 4.3]. -/
def decode (C : FnClass) (q : PolyExpr) (κ : ℕ) (w : List Bool) : Commitment C q κ where
  publicInput i := w.getD i.val false
  privateInput i := w.getD (C.pubLen.eval κ + i.val) false
  functions j i := w.getD
    (C.pubLen.eval κ + C.privLen.eval κ + j.val * C.fnLen.eval κ + i.val) false
  state := w.drop (C.pubLen.eval κ + C.privLen.eval κ + q.eval κ * C.fnLen.eval κ)

/-- The commitment parser reads the displayed windows and retains their remaining suffix. -/
theorem decode_eq (C : FnClass) (q : PolyExpr) (κ : ℕ) (w : List Bool) :
    decode C q κ w =
      ⟨(fun i => w.getD i.val false),
        (fun i => w.getD (C.pubLen.eval κ + i.val) false),
        (fun j i => w.getD
          (C.pubLen.eval κ + C.privLen.eval κ + j.val * C.fnLen.eval κ + i.val) false),
        w.drop (C.pubLen.eval κ + C.privLen.eval κ + q.eval κ * C.fnLen.eval κ)⟩ := rfl

/-- Derive the simulator's allowed public input and ordered function/value pairs from a
commitment [GJLS21, Definition 4.3; Theorem 9.2 proof, Hybrid 1]. -/
def omega (a : Commitment C q κ) (S : FEScheme.Raw C) (pp : PublicParams S.G κ) :
    S.Omega κ pp where
  count := q.eval κ
  publicInput := a.publicInput
  functions := a.functions
  values j := C.eval κ (S.cprm κ pp) (a.functions j) a.publicInput a.privateInput

/-- Allowed information retains the committed functions and evaluates them on the input. -/
theorem omega_eq (a : Commitment C q κ) (S : FEScheme.Raw C)
    (pp : PublicParams S.G κ) :
    a.omega S pp = ⟨q.eval κ, a.publicInput, a.functions,
      fun j => C.eval κ (S.cprm κ pp) (a.functions j) a.publicInput a.privateInput⟩ := rfl

end Commitment

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
