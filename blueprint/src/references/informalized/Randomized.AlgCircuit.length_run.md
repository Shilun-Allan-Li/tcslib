<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.length_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a circuit run

**Claim.** Executing a finite list of arithmetic gates in order produces a list of values with exactly as many entries as there are gates.

**Proof.** Use induction by removing the last gate. The empty gate list produces the empty value list. For a list formed by appending a gate $g$ to $gs$, the run is the run of $gs$ followed by the single value obtained by evaluating $g$ on that prior run (`run_append_singleton`). Hence its length is the length of the run of $gs$ plus one; the induction hypothesis identifies that length with $|gs|$, giving the claim.

**Key facts.** `Randomized.AlgCircuit.run_append_singleton`.
