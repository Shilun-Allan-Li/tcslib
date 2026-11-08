<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Machine.lean :: Complexity.LogProg.TQBFARM.St.toV_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero State Register Vector

**Claim.** The register vector of the zero state is the constant function on the seven registers with value $0$.

**Proof.** To show the two functions agree, fix any register index. The proof checks each of the seven possible indices. At each one, the constant function has value $0$, and the corresponding field of the zero state is also $0$. Hence the functions agree at every index and are equal.
