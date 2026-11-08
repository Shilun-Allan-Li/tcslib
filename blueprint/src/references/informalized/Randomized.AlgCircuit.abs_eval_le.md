<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.abs_eval_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit output magnitude bound

**Claim.** If the integer inputs have magnitude at most $X$ for $X\ge1$, then a circuit’s output has magnitude at most $(2X)^{2^{\operatorname{size}(C)}}$.

**Proof.** Use the sharper circuit bound with input bound $2X$. Since $X\ge1$, we have $2X\ge2$, and the original input magnitudes, bounded by $X$, are also bounded by $2X$. The sharper bound therefore gives $|C(x)|\le (2X)^{2^{\operatorname{size}(C)}}$, as required.

**Key facts.** `Randomized.AlgCircuit.abs_eval_le_pow`.
