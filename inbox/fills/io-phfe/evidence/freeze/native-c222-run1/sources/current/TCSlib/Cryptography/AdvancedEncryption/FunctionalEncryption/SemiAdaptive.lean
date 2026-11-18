/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Data
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Games
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Security
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Semi-adaptive functional-encryption security

## Contents

* `Data`: bounded oracle adversaries and the fixed-width machine adapter.
* `Simulator`: raw stateful algorithms and uniform efficiency.
* `Games`, `Security`: exact experiments and security predicates.
* `FromTwoStage`: the raw simulator conversion and exact committed-game identity.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  Definitions 4.1-4.3 and 4.6, Section 9 and Theorems 10.3-10.4.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive 2020/1420, Sections 2-4 and Appendix B.
* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, CRYPTO 2020; full version, Cryptology ePrint Archive 2020/762,
  Lemma 2 and Appendix A, (28)-(32).
* [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, ICALP 2014;
  full version, Cryptology ePrint Archive 2014/995, Definition 1 and Theorem 3.
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, 2026, Section 1.4 and Theorem 5.1.
-/
