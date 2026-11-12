/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.MPC.ArithmeticCircuit
import TCSlib.Cryptography.MPC.BGW

/-!
# Secure multiparty computation

## Contents

* `TCSlib.Cryptography.MPC.ArithmeticCircuit`: arithmetic circuits, the function class that
  secure computation protocols are stated for.
* `TCSlib.Cryptography.MPC.BGW`: the BGW protocol over Shamir sharings.

## References

* [BGW88] M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness theorems for non-cryptographic
  fault-tolerant distributed computation*, STOC 1988.
-/
