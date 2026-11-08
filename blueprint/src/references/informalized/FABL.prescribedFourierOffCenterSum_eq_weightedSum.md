<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.prescribedFourierOffCenterSum_eq_weightedSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Off-center sum as a weighted sum

**Claim.** The sum over cube points $a\ne x$ of the real value of $f(a)$ times the prescribed Fourier kernel at $(a,x)$ equals the sum over all cube points with the kernel factor replaced by zero at $a=x$.

**Proof.** Rewrite the sum restricted by $a\ne x$ as a sum over the cube with the point $x$ erased. First commute the two factors in each summand. On the erased set, every point differs from $x$, so inserting the factor that is $0$ at $x$ and otherwise the kernel does not change any term. Finally, extend the sum from the erased set to the whole cube: the only added point is $x$, and its new summand is zero. This yields the claimed weighted sum.
