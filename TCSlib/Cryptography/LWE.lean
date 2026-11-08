/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Noise
import TCSlib.Cryptography.LWE.Basic
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.LWE.Encoding
import TCSlib.Cryptography.LWE.Assumption
import TCSlib.Cryptography.LWE.SampleSchedules
import TCSlib.Cryptography.LWE.BitEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Learning with errors: experiments and the decisional assumption

## Contents

* `Noise`: finite-seed scalar integer noise, with an explicit support-bound predicate.
* `Basic`: numeric parameters and the common-secret sample map.
* `Experiments`: the concrete decisional distinguishing experiment.
* `Encoding`: canonical fixed-width challenges with proved length and injectivity.
* `Assumption`: polynomial representation budgets and fixed-sample hardness against `NUPPT`.
* `SampleSchedules`: explicit sample-count substitution and multi-message row accounting.
* `BitEncoding`: bit codepoints, exact tie conventions and bounded-error decoding statements.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3.
-/
