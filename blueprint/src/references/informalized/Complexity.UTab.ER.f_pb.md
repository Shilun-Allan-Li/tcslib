<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_pb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free input position lookup

**Claim.** For a register record $e$, the function assigning its eleven fields to indices $0$ through $10$ has value $e.pb$ at index $9$, the position in the free part of the input.

**Proof.** By definition, index $9$ is assigned the free input position $e.pb$. Since $rPB$ is index $9$, the function's value there is $e.pb$.
