/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Simulation.Games
import TCSlib.Cryptography.Foundations.Subexponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Committed simulation security

Security names one universal stateful simulator before either adversarial machine and before
the polynomial number of committed keys. Raw security predicates expose a specified raw
simulator. The public security notions quantify over simulators with uniform efficiency.

## Main definitions

* `FEScheme.Raw.SimSecureWith`, `SimSecure`: negligible committed simulation advantage.
* `FEScheme.Raw.SubexpSimSecureWith`, `SubexpSimSecure`: one common positive exponent.

## Main results

The proposition readers make the order of all quantifiers explicit.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, Journal of the ACM, 2026, Section 1.1.
* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definition 4.3 and Remarks 4.3 and 4.6.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

namespace FEScheme.Raw

variable {C : FnClass} (S : FEScheme.Raw C)

/-- A specified raw simulator gives negligible advantage against every pair of non-uniform
PPT machines and every polynomial key count [GJLS21, Definition 4.3; Remark 4.6].
The scheme and its polynomial parameter families are fixed before this predicate;
negligibility is familywise, with no bound uniform over all such families. -/
def SimSecureWith (Sim : Simulator.Raw S) : Prop :=
  ∀ A : TwoStage, ∀ q : PolyExpr, Negligible (S.simAdv Sim A q)

/-- Raw simulation security is negligible advantage for every machine pair and key count. -/
theorem simSecureWith_iff (Sim : Simulator.Raw S) :
    S.SimSecureWith Sim ↔ ∀ A : TwoStage, ∀ q : PolyExpr, Negligible (S.simAdv Sim A q) :=
  Iff.rfl

/-- Public-key simulation security has one efficient, stateful simulator before all
adversaries and key counts [GJLS21, Definition 4.3, epsilon one; Remark 4.6]. -/
def SimSecure : Prop := ∃ Sim : Simulator S, S.SimSecureWith Sim.toRaw

/-- Simulation security quantifies over the efficient simulator interface. -/
theorem simSecure_iff :
    S.SimSecure ↔ ∃ Sim : Simulator S, S.SimSecureWith Sim.toRaw := Iff.rfl

/-- A specified raw simulator has one positive subexponential exponent before every
adversary and polynomial key count [JLS26, Section 1.1; GJLS21, Definition 4.3]. -/
def SubexpSimSecureWith (Sim : Simulator.Raw S) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : TwoStage, ∀ q : PolyExpr, SubexpSmall c (S.simAdv Sim A q)

/-- The subexponential exponent precedes the adversaries and the key count. -/
theorem subexpSimSecureWith_iff (Sim : Simulator.Raw S) :
    S.SubexpSimSecureWith Sim ↔
      ∃ c : ℝ, 0 < c ∧ ∀ A : TwoStage, ∀ q : PolyExpr, SubexpSmall c (S.simAdv Sim A q) :=
  Iff.rfl

/-- Subexponential simulation security has one efficient universal simulator and one
positive common security exponent [JLS26, Section 1.1; GJLS21, Definition 4.3]. -/
def SubexpSimSecure : Prop := ∃ Sim : Simulator S, S.SubexpSimSecureWith Sim.toRaw

/-- Subexponential security quantifies over an efficient simulator. -/
theorem subexpSimSecure_iff :
    S.SubexpSimSecure ↔ ∃ Sim : Simulator S, S.SubexpSimSecureWith Sim.toRaw := Iff.rfl

/-- Subexponential raw simulation security implies negligible raw simulation security.

**Proof sketch.** Use the shared implication from subexponential smallness to negligibility
for each machine pair and query polynomial, at the common positive exponent. -/
theorem SubexpSimSecureWith.simSecureWith {Sim : Simulator.Raw S}
    (h : S.SubexpSimSecureWith Sim) : S.SimSecureWith Sim :=
  Exists.elim ((S.subexpSimSecureWith_iff Sim).1 h) fun _ hc =>
    (S.simSecureWith_iff Sim).2 fun A q =>
      SubexpSmall.negligible (hc.2 A q) hc.1

end FEScheme.Raw

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
