/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage
import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import TCSlib.CommunicationComplexity.DeterministicCC.Rectangle
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle
import TCSlib.CommunicationComplexity.DeterministicCC.Rank
import TCSlib.CommunicationComplexity.DeterministicCC.Transcript
import TCSlib.CommunicationComplexity.DeterministicCC.Trees
import TCSlib.CommunicationComplexity.DeterministicCC.Subprotocol
import TCSlib.CommunicationComplexity.DeterministicCC.BalancedSimulation
import TCSlib.CommunicationComplexity.DeterministicCC.DetComposition
import TCSlib.CommunicationComplexity.DeterministicCC.UpperBounds
import TCSlib.CommunicationComplexity.DeterministicCC.OneWay
import TCSlib.CommunicationComplexity.DeterministicCC.Helper
import TCSlib.CommunicationComplexity.DeterministicCC.Hamming
import TCSlib.CommunicationComplexity.DeterministicCC.BitString
import TCSlib.CommunicationComplexity.DeterministicCC.FuncEquality
import TCSlib.CommunicationComplexity.DeterministicCC.FuncDisjointness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deterministic Two-Party Communication Complexity

## Main results

- `Deterministic.communicationComplexity_le_iff`: characterizes when communication complexity is bounded by a given value
- `Deterministic.rectangle_partition`: every protocol induces a rectangle partition of the input space
- `Deterministic.clog_ncard_le_communicationComplexity`: fooling-set lower bound via log of the fooling set size
- `Deterministic.Rank.clog_boolFunctionRank_le_communicationComplexity`: rank lower bound via log of the Boolean function matrix rank
- `Deterministic.Protocol.exists_balanced_simulation`: balanced-simulation theorem for deterministic protocols

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity.Deterministic

end CommunicationComplexity.Deterministic
