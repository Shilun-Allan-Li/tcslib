<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonFlatMap_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Bit of a Flattened List

**Claim.** If a nonempty list of elements is mapped to Boolean words each ending in $0$, then the concatenation of those words also ends in $0$.

**Proof.** Since $L$ is nonempty, write it as $L' ++ [a]$, where $a$ is its last element. By hypothesis, $f(a)=u++[0]$ for some word $u$. Flattening the map over the concatenation gives $L'.flatMap(f) ++ f(a)$, which is therefore $(L'.flatMap(f) ++ u) ++ [0]$. Thus the flattened list ends in $0$.
