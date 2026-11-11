/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Implications.PublicKey

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implications

The catalog of end-to-end results: an explicit set of hardness assumptions implies the existence of
a fundamental primitive with a precise security notion. Each entry states its full assumption set
and is proved by a short composition of published results; definitions, candidates and reductions
never import this layer.

## Contents

* `PublicKey`: adaptive multi-message IND-CPA public-key encryption with `n`-bit messages, from RSA
  and from factoring.
-/
