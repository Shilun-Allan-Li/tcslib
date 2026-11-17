/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Gadget
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Eval
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Symmetric
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# GSW homomorphic encryption from LWE: leveled, bootstrapped, and pure and leveled FHE

The folder also covers NAND bootstrapping, pure and leveled fully homomorphic encryption,
their security statements and the polynomial modulus-to-noise ratio (phase 6b).

## Contents

* `Gadget`: parameters, the gadget `G = I ⊗ gᵗ` and deterministic binary decomposition `G⁻¹`.
* `Noise`: the key-agnostic invariant `tᵗC = x·tᵗG + e`, asymmetric multiplication, NAND,
  sums and right-associative product chains.
* `Scheme`: public-key GSW on the existing Regev/LWE key, fresh noise and decryption.
* `Eval`: homomorphic evaluation of `BoolCircuit.DAGCircuit` and leveled correctness.
* `Security`: concrete IND-CPA hybrids from DLWE and column leftover hashing.
* `Symmetric`: batched secret-key GSW and its direct DLWE bound (optional unit).
* `Branching`: the homomorphic selector and the evaluation of permutation branching programs
  and of formulas through Barrington's construction.
* `DecryptFormula`: the key bits, decryption as a formula in them, and the augmented NAND
  formula with its depth.
* `Bootstrap`: NAND bootstrapping, pure FHE evaluation of NAND-form and fan-in-2 circuits, and
  the evaluation key.
* `Circular`: the FHE view and concrete, per-distinguisher weak circular security.
* `Leveled`: the leveled scheme, a consecutive key chain over layered NAND circuits.
* `LeveledSecurity`: IND-CPA of the leveled scheme from DLWE by a top-down key hybrid.
* `PolyRatio`: GSW parameters of an LWE family and correctness at a polynomial ratio.
* `Asymptotic`: encodings, the asymptotic hypotheses and asymptotic IND-CPA statements.

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, Section 6.1.3.
* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094, version dated 13 June 2014, Section 3.
-/
