<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.sqrt_violaError -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square Root of the Viola Error

**Claim.** For $0\leq\varepsilon\leq1$ and $1\leq d$, the square root of $V(\varepsilon,d)$ equals one third of $V(\varepsilon,d+1)$.

**Proof.** The successor formula for the Viola error gives $V(\varepsilon,d+1)=3\sqrt{V(\varepsilon,d)}$ under the stated hypotheses (`violaError_succ`). Rearranging this identity yields the claim.

**Key facts.** `FABL.violaError_succ`.
