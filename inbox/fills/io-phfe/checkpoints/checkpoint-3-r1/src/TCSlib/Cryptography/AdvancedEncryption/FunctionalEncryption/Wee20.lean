/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.PHFE
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity.Compose
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity.Slack
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearCorrect
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSecurity
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.LinearSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticCorrect
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSecurity
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.QuadraticSimulator
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Wire
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireDraws
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.WireLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quadratic PHFE from symmetric DLIN

## Contents

* `Wee20.WireLemmas`: length and faithfulness adapters to the existing group-matrix encoder.

* `Linear`, `LinearCorrect`, `LinearSimulator`: the internal building block.
* `LinearSecurity`: explicit adaptive games, fresh-law coupling and deterministic reductions.
* `Quadratic`, `QuadraticCorrect`, `QuadraticSimulator`: the outer typed construction.
* `QuadraticSecurity`: outer hybrids, reductions and explicit DLIN composition.
* `PHFE`: the GJLS21 class, generic-game adapters and public headlines.
* `Targets`: named uniform-efficiency obligations and pure assembly.

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
