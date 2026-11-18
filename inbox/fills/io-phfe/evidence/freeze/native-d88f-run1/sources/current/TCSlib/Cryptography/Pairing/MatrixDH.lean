/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.Pairing.MatrixDH.Diagonal
import TCSlib.Cryptography.Pairing.MatrixDH.FiniteLinear
import TCSlib.Cryptography.Pairing.MatrixDH.AdaptiveShear
import TCSlib.Cryptography.Pairing.MatrixDH.ColumnLaws
import TCSlib.Cryptography.Pairing.MatrixDH.Defs
import TCSlib.Cryptography.Pairing.MatrixDH.Hardness
import TCSlib.Cryptography.Pairing.MatrixDH.SelfReduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform-matrix Diffie-Hellman from decisional linear

## Contents

* `Parameters`: generated group descriptions and public nonidentity generators.
* `Diagonal`: exact finite-field bounds for random diagonal masks.
* `FiniteLinear`: uniform matrix images and exact small-row rank estimates.
* `AdaptiveShear`: kernel-valued translations preserving a public projection.
* `ColumnLaws`: exact canonical real/random column comparisons.
* `Defs`: uniform-matrix experiments and their two-experiment advantage.
* `Hardness`: mathematical closure of polynomial-loss advantage bounds.
* `SelfReduction`: explicit column-hybrid preprocessing, advice, and advantage inequalities.

## References

* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Section 2.1,
  citing Escala et al. for the implication from k-Lin to uniform-matrix MDDH.
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, Journal of the ACM 73(1), Article 1, 2026, Section 1.1.
-/
