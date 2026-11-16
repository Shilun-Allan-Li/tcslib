/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- DRAFT (briefs/lattice-gsw): not compiled.
import TCSlib.Cryptography.Encryption.Homomorphic.GSW.Gadget
import TCSlib.Cryptography.Encryption.Homomorphic.GSW.Noise
import TCSlib.Cryptography.Encryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Encryption.Homomorphic.GSW.Eval
import TCSlib.Cryptography.Encryption.Homomorphic.GSW.Security
import TCSlib.Cryptography.Encryption.Homomorphic.GSW.Symmetric

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Leveled GSW homomorphic encryption from LWE

## Contents

* `Gadget`: parameters, the gadget `G = I ⊗ gᵗ` and deterministic binary decomposition `G⁻¹`.
* `Noise`: the key-agnostic invariant `tᵗC = x·tᵗG + e`, asymmetric multiplication, NAND,
  sums and right-associative product chains.
* `Scheme`: public-key GSW on the existing Regev/LWE key, fresh noise and decryption.
* `Eval`: homomorphic evaluation of `BoolCircuit.DAGCircuit` and leveled correctness.
* `Security`: concrete IND-CPA hybrids from DLWE and column leftover hashing.
* `Symmetric`: batched secret-key GSW and its direct DLWE bound (optional unit).

## References

* [GSW13] C. Gentry, A. Sahai, B. Waters, CRYPTO 2013; author version dated 8 June 2013.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016, Section 6.1.3.
* [AP14] J. Alperin-Sheriff, C. Peikert, ePrint 2014/094, version dated 13 June 2014, Section 3.
