<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Recursion.lean :: Complexity.LogProg.SavitchARM.push_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound for a Pushed Endpoint

**Claim.** If $i+1\le w$, the existing endpoint stack is below $2^{w(w-(i+1))}$, and the new endpoint is below $2^w$, then appending that endpoint gives a stack below $2^{w(w-i)}$.

**Proof.** From $i+1\le w$, we have $w-i=(w-(i+1))+1$, so $w(w-i)=w(w-(i+1))+w$. Thus the target power of two factors as $2^{w(w-(i+1))}2^w$. Since $SE<2^{w(w-(i+1))}$, multiplying by $2^w$ gives $(SE+1)2^w\le 2^{w(w-(i+1))}2^w$. Expanding the left side yields $SE\,2^w+2^w$; the assumption $v<2^w$ therefore implies $SE\,2^w+v<2^{w(w-i)}$.
