<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.corollary9_31_ltf_close_to_junta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Threshold Approximation by Juntas

**Claim.** Every linear threshold function admits a junta approximation with error at most $\epsilon$ and a coordinate set whose size satisfies the stated bound.

**Proof.** Apply the improved Friedgut junta theorem (`ltf_improvedFriedgut_junta`) to the given linear threshold function and the parameters $\epsilon,\eta$. It supplies a set $J$ and a Boolean function $g$ with the required size bound, Fourier concentration, junta property, and approximation error. Discarding the Fourier concentration conclusion leaves exactly the three required properties.

**Key facts.** `FABL.ltf_improvedFriedgut_junta`.
