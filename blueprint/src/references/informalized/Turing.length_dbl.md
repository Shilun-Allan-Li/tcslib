<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.length_dbl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a doubled word

**Claim.** For every bit string $w$, its doubling has length $2$ times the length of $w$.

**Proof.** Induct on $w$. The empty word and its doubling both have length zero. For a word $b::w$, doubling produces the two copies of $b$ followed by the doubling of $w$, so its length is $2+(\mathrm{dbl}(w)).\mathrm{length}$. Applying the induction hypothesis gives $2+2|w|=2|b::w|$.
