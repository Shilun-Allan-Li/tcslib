<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/StatisticalDistance.lean :: TCSlib.InformationTheory.statDist_comm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Statistical Distance

**Claim.** For distributions $p$ and $q$ on a finite set, their statistical distance is symmetric: $d_{\mathrm{stat}}(p,q)=d_{\mathrm{stat}}(q,p)$.

**Proof.** In the defining sum, each summand is $|p(a)-q(a)|$. Reversing the subtraction changes its sign, but absolute value is unchanged: $|p(a)-q(a)|=|q(a)-p(a)|$. Thus the sums, and hence their common factor of $1/2$, agree.
