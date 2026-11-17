<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_choice_certificate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice-word certificates for a decided language

**Claim.** Under the stated halting and acceptance assumptions for $N$, a binary string $x$ belongs to $L$ exactly when there is a choice word $u$ of length $a\cdot2^{(|x|+1)^c}$ such that $xu$ belongs to the choice-word verifier language for $N,a,c$.

**Proof.** The decision hypothesis first identifies membership in $L$ with acceptance using a choice word of length $a\cdot2^{|x|^c}$. The machine halts on every word of that length, and the larger padded budget is at least as large by monotonicity of the exponential budget (\texttt{Complexity.e3_choice_budget}). For a machine that halts within the smaller bound, allowing the larger bound does not change whether it accepts: every longer choice word has the same run as its initial segment of the smaller prescribed length, since the machine has already halted (\texttt{Complexity.acceptsWithin_iff_of_halts}). This yields the equivalent existence of an accepting choice word of the padded length. For each such word $u$, verifier membership of $xu$ is equivalent to the run on $x$ with $u$ halting with output $1$ (\texttt{Complexity.e3_choice_append}). Applying that equivalence in both directions gives the desired certificate characterization.

**Key facts.** `Complexity.acceptsWithin_iff_of_halts`, `Complexity.e3_choice_budget`, `Complexity.e3_choice_append`.
