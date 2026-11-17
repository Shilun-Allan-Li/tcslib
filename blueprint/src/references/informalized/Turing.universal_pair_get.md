<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_pair_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubled Pairing Bits

**Claim.** For each position $j$ within $\alpha$, the paired encoding has the bit $\alpha[j]$ at both positions $2j$ and $2j+1$.

**Proof.** Induct on $\alpha$, allowing $j$ to vary. The empty string case is impossible because $j<|\alpha|$. For $\alpha=b::\alpha'$, if $j=0$, the first two entries of the doubled prefix are both $b$, so both lookups give the head bit. If $j=j'+1$, the length hypothesis gives $j'<|\alpha'|$. Removing the first two entries of the encoding shifts both requested positions down by two; the induction hypothesis then says both entries are $\alpha'[j']$, as required.
