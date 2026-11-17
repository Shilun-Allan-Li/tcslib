<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.strictMono_standardGaussianUpperTailOpen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict decrease of the Gaussian upper tail

**Claim.** The standard Gaussian upper-tail function, taking $t$ to $1-\Phi(t)$, is strictly decreasing, and its values lie in $(0,1)$.

**Proof.** For $x<y$, strict antitonicity of the standard Gaussian upper-tail function gives $1-\Phi(x)>1-\Phi(y)$ (\(`FABL.standardGaussianUpperTail_strictAnti`\)). The map into the open interval $(0,1)$ uses the already established positivity and strict upper bound in the definition of the bundled function.

**Key facts.** `FABL.standardGaussianUpperTail_strictAnti`.
