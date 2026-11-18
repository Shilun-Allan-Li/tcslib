/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Assembly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient public-key PHFE headlines

The concrete efficiency targets assemble the efficient scheme and both simulators.
The raw bounds discharge correctness and simulation security. Only the L2 realisability
of machine-derived adversaries remains a reduction hypothesis; the shared L1 target
supplies matrix-DH realisers. No efficient primitive is constructed in this module.

## Main definitions

This module introduces no new algorithm or target.

## Main results

* `wee20PHFE_correct`, `wee20PHFE_correctExcept_zero`: exact exponent correctness.
* `wee20PHFE_simSecure`, `wee20PHFE_saSimSecure`: security with efficient simulators.
* `wee20PHFE_subexpSimSecure`, `wee20PHFE_subexpSASimSecure`: common-exponent security.
* `wee20PHFE_gjls21`: the Definition 4.3 many-key, epsilon-one PHFE package with linear efficiency.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.3 and 4.6, Remarks 4.3 and 4.6,
  Section 9 and Theorems 10.3-10.4.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Section 3, main claim,
  p.6, with Section 3.3, pp.7-8.
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, Journal of the ACM 73(1), Article 1, 2026, Section 1.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20

open Complexity TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

section

variable (G : BilinearGen) (ℓ n : PolyExpr) (d : ℕ) (hT : Targets G ℓ n d)

local notation "PG" => layeredPG_raw ℓ (n.mul n) d
local notation "P" => wee20PHFE G ℓ n d hT.scheme

/-- The assembled PHFE is perfectly correct in the target-group exponent
[GJLS21, Definition 4.2 and Section 9; Wee20, Section 3.1, (4)-(5)]. -/
theorem wee20PHFE_correct : (P).toRaw.Correct :=
  Eq.mpr (congrArg (fun S : FEScheme.Raw (phfeClass ℓ n G.wG d) => (S).Correct)
    (wee20PHFE_toRaw G ℓ n d hT.scheme))
    (wee20PHFE_raw_correct G ℓ n d PG (PHFE.layeredPG_sound ℓ n d))

/-- Perfect exponent correctness gives zero correctness error in GJLS21's syntax
[GJLS21, Definition 4.2]. -/
theorem wee20PHFE_correctExcept_zero : (P).toRaw.CorrectExcept 0 :=
  Eq.mpr (congrArg
    (fun S : FEScheme.Raw (phfeClass ℓ n G.wG d) => (S).CorrectExcept 0)
    (wee20PHFE_toRaw G ℓ n d hT.scheme))
    (wee20PHFE_raw_correctExcept_zero G ℓ n d PG (PHFE.layeredPG_sound ℓ n d))

/-- The assembled primitive has one efficient committed simulator before all machine
pairs and key counts [GJLS21, Definition 4.3, epsilon one; Remark 4.6].

**Proof sketch.** Supply the already assembled wee20Sim using hT.simulators. Use
wee20PHFE_raw_simSecureWith and layeredPG_sound. Instantiate its L1 realisability by
mddhRealizable_of_preTarget G hT.mddh for each polynomial dimension pair. Transport the
scheme and simulator through their assembly readers. No sampler closure is assumed. -/
theorem wee20PHFE_simSecure (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20Realizable43 G ℓ n d PG p hp) (h : G.DLINAssumption) :
    (P).toRaw.SimSecure := sorry

/-- The assembled primitive has one efficient semi-adaptive simulator before every
oracle NUPPT and TOTAL budget [Wee20, Section 2.2].

**Proof sketch.** Supply wee20SASim G ell n d hT.simulators, read its raw identity, and
apply wee20PHFE_raw_saSimSecureWith with layeredPG_sound. Discharge shared L1 matrix
realisability using mddhRealizable_of_preTarget and hT.mddh, then transport the scheme
through wee20PHFE_toRaw. No machine is constructed from an arbitrary typed adversary. -/
theorem wee20PHFE_saSimSecure (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20RealizableSA G ℓ n d PG p hp) (h : G.DLINAssumption) :
    (P).toRaw.SASimSecure := sorry

/-- One efficient committed simulator attains a common positive subexponential exponent
[GJLS21, Definition 4.3; the subexponential convention in JLS26, Section 1.1].

**Proof sketch.** Use wee20PHFE_raw_subexpSimSecureWith and the efficient committed
simulator already assembled from hT.simulators. The raw theorem's exponent is chosen
before the machine pair and key count. Discharge every L1 realisability obligation by
hT.mddh and mddhRealizable_of_preTarget, then use the assembly readers. -/
theorem wee20PHFE_subexpSimSecure (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20Realizable43 G ℓ n d PG p hp) (h : G.SubexpDLIN) :
    (P).toRaw.SubexpSimSecure := sorry

/-- One efficient semi-adaptive simulator attains a common positive subexponential
exponent before every oracle machine and budget [Wee20, Section 2.2].

**Proof sketch.** Use wee20PHFE_raw_subexpSASimSecureWith and the efficient semi-adaptive
simulator assembled from hT.simulators. Discharge L1 realisability by hT.mddh through
the shared link. Read the scheme/simulator raw identities. The common exponent is
independent of the oracle machine and TOTAL call polynomial. -/
theorem wee20PHFE_subexpSASimSecure (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20RealizableSA G ℓ n d PG p hp) (h : G.SubexpDLIN) :
    (P).toRaw.SubexpSASimSecure := sorry

/-- The assembled public-key PHFE has zero correctness error, many-key epsilon-one
simulation security and the one uniform linear-encryption target
[GJLS21, Definitions 4.1-4.3 and 4.6, Remark 4.6 and Section 9].
The class is the original private quadratic polynomial class, with outputs embedded in
GT. The simulator receives allowed scalar values via the recorded Theorem 9.2 Hybrid 1
reading. The positive-size linear-time formulation is specified in LinearEfficient. -/
theorem wee20PHFE_gjls21 (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    (hR : Wee20Realizable43 G ℓ n d PG p hp) (h : G.DLINAssumption) :
    (P).toRaw.CorrectExcept 0 ∧ (P).toRaw.SimSecure ∧ LinearEfficient G :=
  ⟨wee20PHFE_correctExcept_zero G ℓ n d hT,
    wee20PHFE_simSecure G ℓ n d hT p hp hpb hR h, hT.linear⟩

end

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20
