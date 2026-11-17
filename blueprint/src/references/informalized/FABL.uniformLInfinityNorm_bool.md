<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLInfinityNorm_bool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean supremum norm

**Claim.** For a function $f:\{\mathrm{false},\mathrm{true}\}\to\mathbb R$, its supremum norm is $\max\{|f(\mathrm{false})|,|f(\mathrm{true})|\}$.

**Proof.** The Boolean domain consists of exactly $\mathrm{false}$ and $\mathrm{true}$. Thus the supremum of $|f|$ over the domain is the larger of its values at those two points, as claimed.
