/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations
import TCSlib.Cryptography.Pairing.Exponents
import TCSlib.Cryptography.Pairing.Linear
import TCSlib.Cryptography.Pairing.MatrixDH

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and the bilinear Diffie–Hellman assumptions

## Contents

* `Group`: abstract symmetric bilinear groups of prime order, their generators, bilinearity and
  non-degeneracy facts.
* `Assumptions`: the BDH and Decision BDH experiments and assumptions; Decision BDH implies BDH.
* `Operations`: the efficiency contract of a generator (group operations and pairing as
  polynomial-time string functions).

* `Exponents`: known scalar actions and pairing products for implicit matrices.
* `Linear`: symmetric DLIN and its explicit matrix presentation comparison.
* `MatrixDH`: uniform-matrix games and deterministic DLIN self-reduction.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004,
  §2.2 and §3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
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
