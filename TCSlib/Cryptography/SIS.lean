/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SIS.Basic
import TCSlib.Cryptography.SIS.Experiments
import TCSlib.Cryptography.SIS.Encoding
import TCSlib.Cryptography.SIS.Assumption

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Short integer solution: experiments and the hardness assumption

## Contents

* `Basic`: numeric parameters and the nonzero short integer kernel relation.
* `Experiments`: the concrete success probability of an optional integer-vector solver.
* `Encoding`: matrix encodings, signed solver outputs, and admitted representation statements.
* `Assumption`: polynomial representation budgets and success hardness against `NUPPT`.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1.
-/
