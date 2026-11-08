/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.Hashing.SIS.Experiments
import TCSlib.Cryptography.Hashing.SIS.Profiles

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SIS-based binary matrix hashing

## Contents

* `Basic`: binary hashing, integer collision differences and solution/compression statements.
* `Experiments`: the typed collision-probability and direct SIS-success bound.
* `Profiles`: an explicit dyadic profile and its statement-phase obligations.

No hardness is proved. The independent `SISAssumption`, efficient machine adapters and
the future generic CRH-owner bridge remain explicit consumer obligations.
-/
