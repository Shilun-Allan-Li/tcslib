/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.Hashing.SIS.Experiments
import TCSlib.Cryptography.Hashing.SIS.Profiles
import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Hashing.SIS.CollisionOutput
import TCSlib.Cryptography.Hashing.SIS.Implementation
import TCSlib.Cryptography.Hashing.SIS.Asymptotic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIS-based binary matrix hashing

## Contents

* `Basic`: binary hashing, integer collision differences and solution/compression statements.
* `Experiments`: the typed collision-probability and direct SIS-success bound.
* `Profiles`: an explicit dyadic profile and its statement-phase obligations.
* `Universality`: unconditional composite-modulus universality and strong extraction.
* `CollisionOutput`: exact raw-output signed postprocessing and probability bounds.
* `Implementation`: the encoded polynomial-schedule binary matrix-hash evaluator.
* `Asymptotic`: negligible raw collisions under the independent SIS assumption.

No hardness is proved. The independent `SISAssumption`, efficient machine adapters and
the future generic CRH-owner bridge remain explicit consumer obligations.
-/
