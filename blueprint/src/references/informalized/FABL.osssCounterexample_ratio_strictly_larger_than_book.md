<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexample_ratio_strictly_larger_than_book -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict ratio comparison

**Claim.** The ratio $(130+20\sqrt{3})/157$ is strictly less than $(42+2\sqrt{33})/51$.

**Proof.** Since both square roots are nonnegative, squaring preserves the relevant comparisons. The identities $(\sqrt{3})^2=3$ and $(\sqrt{33})^2=33$ show, by direct rational arithmetic, that $\sqrt{3}<1351/780$ and $718/125<\sqrt{33}$. Substituting these bounds into the two sides reduces the desired strict inequality to a rational linear inequality, which holds by arithmetic.
