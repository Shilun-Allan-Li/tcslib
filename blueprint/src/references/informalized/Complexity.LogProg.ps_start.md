<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkProof.lean :: Complexity.LogProg.ps_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path-language decision procedure

**Claim.** The fixed path program from the all-zero configuration terminates within bound $4(|x|+1)$ on every branch and has an accepting branch exactly for inputs satisfying the stated encoding, matrix, source, target, and bounded-walk conditions.

**Proof.** First note that $2|x|+2\le 4(|x|+1)$, so the bound required by the component scans is available. The unary-prefix scan (`ps_unary`) chooses a length $n$ whose doubled unary prefix and separator occur in $x$, then enters the matrix scan. The matrix-suffix scan (`ps_mat`) verifies all $n^2$ aligned matrix pairs and the following separator. If that check succeeds, the existential source-phase scan (`ps_sphase`) chooses $s<n$ and verifies that its binary word appears doubled with a separator at the prescribed position. The target-phase scan (`ps_tphase`) then chooses $t<n$ and verifies the plain binary encoding from that position to the end of the input. At this point the walk theorem (`ps_walk`) gives exactly the remaining condition: a walk from $s$ to $t$ of length at most $n$, using vertices below $n$, whose steps correspond to matrix bits equal to $1$. Each component establishes termination with the same register bound as well as its acceptance condition, so the chained program terminates on every branch and accepts exactly when all these conditions hold. Finally, the resulting conjunctions and existential witnesses are rearranged into the definition of `PathAcc`; the initial register values are zero, as required.

**Key facts.** `Complexity.LogProg.ps_unary`, `Complexity.LogProg.ps_mat`, `Complexity.LogProg.ps_sphase`, `Complexity.LogProg.ps_tphase`, `Complexity.LogProg.ps_walk`, `Complexity.LogProg.NSem.congr`, `Complexity.lt_of_getD_true`, `Turing.length_bits_le_self`.
