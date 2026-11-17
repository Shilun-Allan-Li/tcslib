<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_pt_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality test is polynomial-time computable

**Claim.** For each fixed bit string $w$, the function returning $[1]$ when $x=w$ and $[0]$ otherwise is polynomial-time computable.

**Proof.** The machine that tests equality with a fixed word and outputs one of two fixed words computes the function $x\mapsto [1]$ if $x=w$ and $[0]$ otherwise in linear time (`Turing.FinTM.computesFunInTime_ifEq`). A function computable within a linear time bound is polynomial-time computable (`Complexity.polyTimeComputable_of_linear`). The machine’s two outputs agree with the specified one-bit outputs: if $x=w$, the test selects $[1]$; otherwise it selects $[0]$.

**Key facts.** `Turing.FinTM.computesFunInTime_ifEq`, `Complexity.polyTimeComputable_of_linear`.
