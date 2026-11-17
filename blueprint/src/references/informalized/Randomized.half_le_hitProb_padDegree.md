<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.half_le_hitProb_padDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hit Probability After Degree Padding

**Claim.** For a symmetric relation on $\mathrm{Fin}(n)$, if a length-$k$ walk in its directed graph starting at $s$ hits $t$ with probability at least $9/10$, then the length-$10n^2k$ walk in the padded regular multigraph of degree $\mathrm{le\_padDegree}(n)$ hits $t$ with probability at least $1/2$.

**Proof.** The existence of $s\in\mathrm{Fin}(n)$ implies $n>0$. Take the degree $D=\mathrm{padDegree}(n)$. The degree bounds give $n\le D$ and $D\le 2n$, hence in particular $D\le4n^2$. The bounded-degree padding theorem (`Randomized.half_le_hitProb_padGraph`) applies to this degree and the given symmetric relation and high hit probability, and gives the claimed lower bound for the padded walk. The theorem's degree parameter is exactly $\mathrm{le\_padDegree}(n)$.

**Key facts.** `Randomized.half_le_hitProb_padGraph`, `Randomized.le_padDegree`, `Randomized.padDegree_le`.
