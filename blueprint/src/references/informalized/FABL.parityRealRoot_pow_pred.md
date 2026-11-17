<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityRealRoot_pow_pred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power of the parity real root

**Claim.** For natural numbers $n$ and $h$ with $h>0$, if $r=n^{1/h}$, then $r^{h-1}=n^{1-1/h}$.

**Proof.** Write $r=n^{1/h}$. The rule for raising a real power to a natural power gives $r^{h-1}=n^{(1/h)(h-1)}$. Since $h>0$, it is nonzero, and elementary fraction arithmetic yields $(1/h)(h-1)=1-1/h$. Substitution gives the claimed identity.
