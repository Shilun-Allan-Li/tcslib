<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.one_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Codec Execution

**Claim.** For every input bit string $y$ and every codec mode other than the step mode, either there is a representation satisfying the stated shape and preliminary checks for which the codec program reaches its scan-completion state with the specified bounded registers, or every representation of the required shape fails those checks and the program halts with answer false, respecting its precondition and register bound throughout.

**Proof.** 1. First parse the input. The parsing theorem (`parse_run`) gives either a representation $y=\langle x,\langle w,\mathrm{bits}(s)\rangle\rangle$ with the length bound on $\mathrm{bits}(s)$, together with a bounded run from the initial length scan to the counter-halving stage and the associated parsed register values, or it shows that no representation of this shape exists and that the program halts false. In the latter case the second alternative follows immediately.

2. In the representation case, the encoding-length formula (`Turing.length_pairEncode`) expresses $|y|$ in terms of $|x|$, $|w|$, and $|\mathrm{bits}(s)|$. The bound on the bit length of $s$ then gives $s\leq 2|y|$ (`s_le_of_width`), so the global register bound is large enough for the subsequent execution (`bnd_ge`). The bounds on the parsed counters and the initial registers produce a bounded intermediate register record.

3. The representation of $y$ is unique: applying injectivity of pair encoding twice identifies the two outer components and then the inner components; injectivity of the binary representation identifies $s$ (`pairEncode_inj`, `bits_injective`). This uniqueness lets any later failure for the parsed representation imply failure for every representation in the statement.

4. The layout analysis (`layout_run`) now divides the execution into two cases. Either the required length, marker, and payload checks hold, and the program reaches the comparison phase with the position register equal to the value of the payload bits; or one of the length and marker checks fails, in which case the program halts false. In the failure case, uniqueness shows that no other shaped representation can pass the checks.

5. In the successful layout case, the payload value is strictly less than the corresponding power of two (`bitsVal_lt_two_pow`). The binary-width bound (`two_pow_bits_le`), together with the bound on the width of $x$ (`wP_le`), yields the required numerical bound on that value. If it is at most $|x|+1$, the first branch of the phase analysis (`le_phase`) reaches the scan stage. The scan execution theorem (`vscan_run`) then constructs the scan state for the first $W(2s+1)$ bits of $w$ and continues to the stated completion label. Concatenating these execution segments uses transitivity of reachability (`Reach.trans`). The resulting register record has the claimed values and satisfies the global bound by the established arithmetic estimates.

6. If instead the payload value exceeds $|x|+1$, the other branch of `le_phase` gives a false halt. The representation uniqueness proves that every shaped representation fails the payload check, and chaining the earlier execution segments transfers that halt back to the initial configuration (`AReach.halt`). Thus either the specified successful scan is reached or all shaped representations fail and the program halts false, as claimed.

**Key facts.** `Complexity.Codec.parse_run`, `Complexity.Codec.s_le_of_width`, `Complexity.Codec.bnd_ge`, `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`, `Complexity.Codec.layout_run`, `Complexity.Codec.bitsVal_lt_two_pow`, `Complexity.Codec.two_pow_bits_le`, `Complexity.Codec.wP_le`, `Complexity.Codec.le_phase`, `Complexity.Codec.vscan_run`, `Complexity.Codec.Reach.trans`, `Complexity.LogProg.AReach.halt`, `Turing.length_pairEncode`.
