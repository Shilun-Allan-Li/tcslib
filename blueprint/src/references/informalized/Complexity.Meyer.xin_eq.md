<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.xin_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed index agrees with shifted word

**Claim.** For every integer displacement $d$, the stated signed-index expression equals the symbol of $x$ shifted to position $1+d$.

**Proof.** Unfold the shifted lookup and split on the sign of $d$. If $d<0$, then $d$ is nonzero, so the left-hand expression is blank; the shifted position $1+d$ is below $1$, hence its lookup is also blank. If $d\ge0$, then $1+d$ is a valid shifted position and its list index is exactly $d$. When $d<|x|$, the assumed agreement of $xb$ with the entries of $x$ identifies the two returned symbols. When $d\ge|x|$, both expressions are blank because the list lookup is out of range.
