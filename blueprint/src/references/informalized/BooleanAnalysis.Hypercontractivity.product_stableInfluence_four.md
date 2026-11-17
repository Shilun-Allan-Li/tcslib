<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_stableInfluence_four -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence bound at one third

**Claim.** For a Boolean function on a finite product space whose coordinate atom masses are at least \(\lambda\), the stable influence at rate \(\sqrt{\lambda}/3\), multiplied by that rate, is at most the ordinary influence raised to the power \(3/2\).

**Proof.** Set \(\rho=\sqrt{\lambda}/3\), which is nonnegative. At \(q=4\), the general stable-influence estimate applies whenever \(\rho\le (q-1)^{-1}\lambda^{1-2/q}\); here the right side is \(\sqrt{\lambda}/3\), so the required bound holds. It gives \(\rho I_i^{(\rho)}(f)\le I_i(f)^{3/2}\). By the definition of stable influence, multiplying its sum by \(\rho\) changes each term with \(i\in S\) from \(\rho^{|S|-1}\) to \(\rho^{|S|}\): such an \(S\) has cardinality at least one. This is exactly the sum in the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_stableInfluence`.
