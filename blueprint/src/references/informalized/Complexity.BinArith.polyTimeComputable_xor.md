<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_xor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bitwise Exclusive OR

**Claim.** If the bit-valued functions $p$ and $q$ have polynomial-time computable singleton-list outputs, then the function returning the singleton list containing $p(x)\mathbin{\mathrm{xor}}q(x)$ is polynomial-time computable.

**Proof.** Use the polynomial-time conditional-selection theorem with condition $p$, true branch $[\neg q(x)]$, and false branch $[q(x)]$. The condition is polynomial-time computable by hypothesis, and the two branches are polynomial-time computable by closure under Boolean negation and the hypothesis for $q$ (`Complexity.polyTimeComputable_not`). If $p(x)$ is true, exclusive OR equals $\neg q(x)$; if $p(x)$ is false, it equals $q(x)$. Thus the selected singleton list is exactly $[p(x)\mathbin{\mathrm{xor}}q(x)]$.

**Key facts.** `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_not`.
