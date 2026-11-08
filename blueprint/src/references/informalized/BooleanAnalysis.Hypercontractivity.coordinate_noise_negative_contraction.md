<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Contraction.lean :: BooleanAnalysis.Hypercontractivity.coordinate_noise_negative_contraction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative coordinate-noise contraction

**Claim.** For every $q\ge2$, one can choose $0<c\le1$, with $c=2/5$ when $q=4$, so that negative coordinate noise contracts the $q$-norm on every finite product space.

**Proof.** First choose $c$ using the scalar contraction inequality: for every real $z$, $|1-cz|^q\le |1+z|^q-q(1+c)z$. This choice has $0<c\le1$ and the specified value at $q=4$. The conditional negative-moment inequality applies this scalar bound to the conditional expectation and shows that the $q$th absolute moment of $Cf-c(f-Cf)$ is at most that of $f$, where $C$ averages over the coordinate being updated. Since $N_{i,-c}f=Cf-c(f-Cf)$, this is the required moment comparison. Both moments are nonnegative because the product weights are nonnegative and absolute-value powers are nonnegative. Raising the comparison to the nonnegative power $1/q$ preserves its order, yielding the asserted norm contraction.

**Key facts.** `BooleanAnalysis.Hypercontractivity.CenteredContraction.scalar_contraction`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_negative_moment_le`.
