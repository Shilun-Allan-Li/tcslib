<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choice_certificate_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice-Word Certificates

**Claim.** Under the stated time-bound and decision hypotheses, $x\in L$ exactly when there is a word $u$ of length $(2a)(|x|+1)^c$ such that $xu$ belongs to the verifier language with parameters $2a,c$.

**Proof.** The decision hypothesis identifies membership in $L$ with acceptance within time $a(|x|^c+1)$. Since this time is at most the prescribed certificate length, the halting hypothesis lets us replace acceptance at the certificate length by acceptance at the original time (`Complexity.acceptsWithin_iff_of_halts`), using the bound `Turing.choiceBudget_le`. Thus membership is equivalent to the existence of a choice word of length $(2a)(|x|+1)^c$ whose run halts with output $[1]$. For each such word, the fixed-split characterization (`Complexity.choiceVerifier_append`), with $C=2a$, identifies exactly that pair of run conditions with membership of $xu$ in the verifier language. Applying this equivalence in either direction proves the claim.

**Key facts.** `Complexity.acceptsWithin_iff_of_halts`, `Turing.choiceBudget_le`, `Complexity.choiceVerifier_append`.
