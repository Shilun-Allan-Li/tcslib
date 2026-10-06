/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.MPC.BGW.Protocol
import TCSlib.Cryptography.MPC.BGW.Privacy

/-!
# The BGW protocol

Semi-honest secure multiparty computation of an arithmetic circuit from Shamir sharings.

## Contents

* `TCSlib.Cryptography.MPC.BGW.Protocol`: the gate-by-gate protocol, the degree reduction step,
  and correctness.
* `TCSlib.Cryptography.MPC.BGW.Privacy`: locality of multiplication-free circuits and the
  resulting perfect privacy against `k - 1` parties.

## References

* [BGW88] M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness theorems for non-cryptographic
  fault-tolerant distributed computation*, STOC 1988.
* [AL17] G. Asharov, Y. Lindell, *A full proof of the BGW protocol for perfectly secure
  multiparty computation*, J. Cryptology 30(1), 2017.
-/
