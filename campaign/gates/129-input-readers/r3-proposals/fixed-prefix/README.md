# Fixed-prefix reuse proposal

Reductions already imports the finite-machine construction transitively.
Its private `prefixTM` is definitionally the public `FinTM.prependTM`.
The exact patch removes the six private declarations that feed
`fixedPair_polyTime`. Its retained statement uses
`FinTM.computesFunInTime_pairEncodeFixed` via
`Complexity.polyTimeComputable_of_linear`. The latter requires one
import of ClassNP.PolyTimePairing in Reductions.

The full owner elaborates on 967bc00f00637312676f438c7f61b14219fa943b. The private replacement
proof passes a three-definition seal with standard axioms. Six controls
close natively and fail under the seal. All six private deletions and
the additional import are proposal scope. START-HERE §2 reserves the
frozen import for Seyoon's ruling.
