<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Turing.FinNDTM.UsesSpace.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of space bounds

**Claim.** If the machine uses at most $s(|x|)$ space on every input and choice word, and $s(n)\le s'(n)$ for every $n$, then it uses at most $s'(|x|)$ space on every input and choice word.

**Proof.** Fix an input $x$ and a choice word $w$. The assumed bound gives space usage at most $s(|x|)$, and the pointwise inequality gives $s(|x|)\le s'(|x|)$. Transitivity yields the desired bound.
