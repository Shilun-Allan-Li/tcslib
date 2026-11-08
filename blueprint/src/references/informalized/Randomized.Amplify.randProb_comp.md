<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.randProb_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Randomized Runs

**Claim.** Under the stated step correspondence, halting, and conditional probability assumptions, the probability that $M$ satisfies $Q$ after $n+m$ bits from $\phi(c)$ is the sum of the probabilities that $o$ is true and false after $n$ bits of $N$, weighted respectively by $g(\mathrm{true})$ and $g(\mathrm{false})$.

**Proof.** Proceed by induction on $n$. For $n=0$, the halting hypothesis says that $c$ is already halted. A halted configuration is unchanged by every run (`runWith_of_halt`), so the probability of the predicate after the extra $m$ bits is $g(o(c))$ by the assumed identity for halted configurations. The probability that the zero-bit run has each Boolean value is deterministic; splitting according to $o(c)$ gives the stated weighted sum.

For the induction step, first handle a configuration $c$ that is already halted. The run of $M$ from $\phi(c)$ is unchanged for any number of bits, and the run of $N$ from $c$ is likewise unchanged. The halting stability assumption allows the extra $m$ bits to be counted as a run from $\phi(c)$; the assumed probability identity and the deterministic value $o(c)$ then give the formula.

If $c$ is not halted, split the first choice bit into true and false. The run probability after one additional bit is the average of the two continuation probabilities (`randProb_runWith_choose`). The step correspondence identifies each successor of $M$ with the image under $\phi$ of the corresponding successor of $N$. For either first bit, every length-$n$ continuation halts in $N$, by applying the original halting assumption to the word formed by prefixing that bit. Thus the induction hypothesis applies to both successors. Finally, the probability of each Boolean value after $n+1$ bits is itself the average of its two first-bit continuation probabilities (`randProb_succ`); distributing the weights and regrouping yields the required identity.

**Key facts.** `Turing.NDTM.runWith_of_halt`, `Randomized.randProb_const`, `Complexity.LogProg.randProb_runWith_mono`, `Randomized.randProb_runWith_choose`, `Randomized.randProb_succ`, `Turing.NDTM.runWith_cons`.
