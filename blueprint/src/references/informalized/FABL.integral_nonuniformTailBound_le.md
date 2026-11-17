<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_nonuniformTailBound_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral Bound for a Rational Tail

**Claim.** For $K\ge0$, the integral of $2K/(1+t^3)$ over $t>0$ is at most $8K$.

**Proof.** Rewrite the integrand as $2K(1+t^3)^{-1}$ and pull the constant $2K$ outside the integral. The integral of $(1+t^3)^{-1}$ over the positive half-line is at most $4$ (\(\texttt{integral\_Ioi\_inv\_one\_add\_cube\_le\_four}\)). Multiplying this bound by the nonnegative constant $2K$ gives the claimed upper bound $8K$.

**Key facts.** `FABL.integral_Ioi_inv_one_add_cube_le_four`.
