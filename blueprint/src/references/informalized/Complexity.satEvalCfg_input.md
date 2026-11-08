<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEvalCfg_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol in a Canonical Configuration

**Claim.** In the canonical evaluation configuration at input offset $i$, the symbol under the input head is the optional $i$-th bit of $w$.

**Proof.** The canonical configuration places the shifted input-head position at $i+1$. The input-symbol lookup uses the position one less than this value, hence reads position $i$ of $w$. The bound $i\le |w|$ ensures the lookup is valid, including the case $i=|w|$, where the optional lookup returns none. This is precisely the canonical-position rule for input symbols (`Turing.FinTM.inputSymbol_at`).

**Key facts.** `Turing.FinTM.inputSymbol_at`.
