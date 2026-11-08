<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStream_parseLit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Parser Round Trip

**Claim.** For every literal $\ell$ over natural-number variable indices and every bit string $r$, parsing the encoding of $\ell$ followed by $r$ returns $\ell$ together with the remainder $r$.

**Proof.** If the variable index is $v$, the encoded literal begins with $v+1$ true bits followed by $\mathrm{false}$, the polarity bit, and $r$. By induction on the number of initial true bits, `takeTrues` removes exactly those $v+1$ bits and returns the rest beginning with the delimiter. Since the count is positive, the parser reads the next two bits as the delimiter and polarity, producing variable index $v$ and leaving exactly $r$.
