<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Cfg.SameOutside.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of tape agreement outside sets

**Claim.** If the first and second configurations agree outside sets $F_j$, and the second and third agree outside sets $F'_j$, then the first and third agree outside $F_j\cup F'_j$ on each tape.

**Proof.** Fix a tape $j$ and a position $q$ outside $F_j\cup F'_j$. Then $q$ is outside each of $F_j$ and $F'_j$. The second and third configurations therefore have equal tape values at $q$, and the first and second configurations also have equal tape values there. By transitivity of equality, the first and third configurations agree at $q$.
