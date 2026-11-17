<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/FiniteLaw.lean :: BooleanAnalysis.Hypercontractivity.FiniteLaw.ae_two_point_of_mass_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-Sure Two-Point Support

**Claim.** If a measurable real-valued random variable has total probability one on the two distinct values $x$ and $y$, then it belongs to $\{x,y\}$ almost surely.

**Proof.** Measurability of $X$ makes the level sets $A=\{\omega:X(\omega)=x\}$ and $B=\{\omega:X(\omega)=y\}$ measurable. They are disjoint because $x\ne y$. Therefore their union has measure $\mu(A)+\mu(B)=1$. In a probability space, a measurable set of measure one holds almost everywhere, so almost every $\omega$ lies in $A\cup B$, which is exactly the assertion that $X(\omega)=x$ or $X(\omega)=y$.
