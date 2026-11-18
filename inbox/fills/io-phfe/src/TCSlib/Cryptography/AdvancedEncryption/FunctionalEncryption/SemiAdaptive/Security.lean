/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games
import TCSlib.Cryptography.Foundations.Subexponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Semi-adaptive simulation security

Security uses one universal efficient stateful simulator before every oracle
NUPPT and every polynomial total-call budget. The raw With predicates name a
specified raw simulator. Core reduction inequalities may separately quantify over
all typed adversaries; machine realisability never does so.

## Main definitions

* `FEScheme.Raw.SASimSecureWith`, `SASimSecure`: negligible simulation advantage.
* `FEScheme.Raw.SubexpSASimSecureWith`, `SubexpSASimSecure`: a common positive exponent.

## Main results

The readers expose all quantifier orders. The subexponential-to-negligible reader
uses the shared Foundations API.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; ePrint 2020/1420, §2.2, p.5.
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, Journal of the ACM, 2026, §1.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

variable {C : FnClass} (S : FEScheme.Raw C)

/-- A specified raw simulator gives negligible advantage against every oracle
NUPPT and polynomial total-call budget. [Wee20, §2.2, p.5]. -/
def SASimSecureWith (Sim : SASimulator.Raw S) : Prop :=
  ∀ A : NUPPT, ∀ q : PolyExpr, Negligible (S.saSimAdv Sim (toSAAdv (S := S) A q))

/-- Raw semi-adaptive security is the displayed negligible-advantage condition. -/
theorem saSimSecureWith_iff (Sim : SASimulator.Raw S) :
    S.SASimSecureWith Sim ↔
      ∀ A : NUPPT, ∀ q : PolyExpr, Negligible (S.saSimAdv Sim (toSAAdv (S := S) A q)) :=
  Iff.rfl

/-- Semi-adaptive simulation security names one efficient simulator before all
oracle machines and budgets. [Wee20, §2.2, p.5]. -/
def SASimSecure : Prop := ∃ Sim : SASimulator S, S.SASimSecureWith Sim.toRaw

/-- Semi-adaptive security quantifies over the efficient simulator interface. -/
theorem saSimSecure_iff :
    S.SASimSecure ↔ ∃ Sim : SASimulator S, S.SASimSecureWith Sim.toRaw := Iff.rfl

/-- A specified raw simulator has one positive subexponential exponent before
all machines and query budgets. [JLS26, §1.1; Wee20, §2.2, p.5]. -/
def SubexpSASimSecureWith (Sim : SASimulator.Raw S) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : NUPPT, ∀ q : PolyExpr,
    SubexpSmall c (S.saSimAdv Sim (toSAAdv (S := S) A q))

/-- The common exponent precedes both the machine and query-budget quantifiers. -/
theorem subexpSASimSecureWith_iff (Sim : SASimulator.Raw S) :
    S.SubexpSASimSecureWith Sim ↔
      ∃ c : ℝ, 0 < c ∧ ∀ A : NUPPT, ∀ q : PolyExpr,
        SubexpSmall c (S.saSimAdv Sim (toSAAdv (S := S) A q)) := Iff.rfl

/-- Subexponential semi-adaptive security uses one efficient universal simulator.
[JLS26, §1.1; Wee20, §2.2, p.5]. -/
def SubexpSASimSecure : Prop :=
  ∃ Sim : SASimulator S, S.SubexpSASimSecureWith Sim.toRaw

/-- The public subexponential notion quantifies over efficient simulators. -/
theorem subexpSASimSecure_iff :
    S.SubexpSASimSecure ↔ ∃ Sim : SASimulator S, S.SubexpSASimSecureWith Sim.toRaw := Iff.rfl

/-- A positive common subexponential exponent implies negligible raw advantage.

**Proof sketch.** Choose the common exponent and apply the shared
SubexpSmall.negligible implication to each oracle machine and total-call budget.
No new asymptotic closure argument is needed. -/
theorem SubexpSASimSecureWith.saSimSecureWith {Sim : SASimulator.Raw S}
    (h : S.SubexpSASimSecureWith Sim) : S.SASimSecureWith Sim :=
  Exists.elim ((S.subexpSASimSecureWith_iff Sim).1 h) fun _ hc =>
    (S.saSimSecureWith_iff Sim).2 fun A q =>
      SubexpSmall.negligible (hc.2 A q) hc.1

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw
