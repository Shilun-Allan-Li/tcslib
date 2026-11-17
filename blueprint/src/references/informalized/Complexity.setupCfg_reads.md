<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_reads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Controller-Tape Reads

**Claim.** In a setup configuration, the symbols read from the budget, unary, and guide tapes are respectively $\beta(b)$, $\mu(u)$, and $\gamma(g)$.

**Proof.** It suffices to check the three possible controller-tape indices. The finite-index case split (`Complexity.finThree_cases`) reduces them to budget, unary, and guide in turn. By the definition of the setup configuration, each index selects its corresponding tape and head position; evaluating the tape there gives, respectively, $\beta(b)$, $\mu(u)$, and $\gamma(g)$.

**Key facts.** `Complexity.finThree_cases`.
