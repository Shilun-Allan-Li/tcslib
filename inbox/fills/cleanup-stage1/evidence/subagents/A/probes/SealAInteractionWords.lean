/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Complexity.ClassP.BinaryArith.Words

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

attribute [local irreducible] Turing.pairEncode Complexity.BinArith.encWords TCSlib.Cryptography.Strategy.encodeMsgs

/-!
# The history encoding as a word list

The string encoding `Strategy.encodeMsgs` of the received-messages component of a view
[PS10, §4.4] is the word-list encoding `Complexity.BinArith.encWords` of the machine layer: both
are the concatenation of the self-delimiting messages `⟨m, []⟩`. The bridge lives in its own
module so that `ZeroKnowledge/Interaction.lean` does not import the binary-arithmetic machines.

## Main results

* `TCSlib.Cryptography.Strategy.encodeMsgs_eq_encWords` — `encodeMsgs L = BinArith.encWords L`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  §4.4.
-/

namespace TCSlib.Cryptography.Strategy

/-- **The history encoding is the word-list encoding:** for every list of words `L`,
`encodeMsgs L = Complexity.BinArith.encWords L` (both are `L.flatMap fun m => ⟨m, []⟩`).
Framework glue, no textbook counterpart. -/
protected theorem encodeMsgs_eq_encWords (L : List (List Bool)) :
    encodeMsgs L = Complexity.BinArith.encWords L := by
  rw [Strategy.encodeMsgs_eq_flatMap, Complexity.BinArith.encWords_def]

end TCSlib.Cryptography.Strategy
