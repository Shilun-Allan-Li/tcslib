<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.card_andFunction_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Outputs of the AND Function

**Claim.** For every natural number $w$, exactly $2^w-1$ sign assignments on $w$ coordinates make the AND function equal to $1$.

**Proof.** There are $2^w$ sign assignments in total. The AND function equals $-1$ precisely when every coordinate is $-1$, so exactly one assignment gives output $-1$. Every output is a sign, hence is either $1$ or $-1$; the assignments giving these two outputs form disjoint sets whose union is the full cube. Consequently the number giving output $1$ is $2^w-1$.
