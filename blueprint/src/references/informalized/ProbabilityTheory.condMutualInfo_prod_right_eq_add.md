<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_prod_right_eq_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional mutual information chain rule

**Claim.** The conditional mutual information between $X$ and $(Y,W)$ given $Z$ equals $I[X:Y\mid Z;\mu]+I[X:W\mid (Y,Z);\mu]$.

**Proof.** Use symmetry of conditional mutual information to exchange its two arguments. The left side becomes the conditional mutual information of $(Y,W)$ with $X$ given $Z$. Apply the chain rule for a pair in the first argument (\texttt{condMutualInfo\_prod\_left\_eq\_add}), obtaining $I[Y:X\mid Z;\mu]+I[W:X\mid (Y,Z);\mu]$. Apply symmetry to each term to put $X$ in the first argument; these are the two terms in the claimed identity.

**Key facts.** `ProbabilityTheory.condMutualInfo_prod_left_eq_add`.

**Caveat.** The symmetry identity used in the proof is not listed among the supplied upstream entries.
