<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse2.lean :: Complexity.LogProg.scanPairs_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Successful Pair Scans

**Claim.** The pair scan started with remembered bit $\ell$ returns $w$ exactly when $z$ consists of doubled bits from a word $u$, followed by $01w$, and the last bit of $u$, if present, or otherwise $\ell$, is not $0$.

**Proof.** For the forward implication, induct on the list $z$ by removing its first two bits at each stage. The empty and one-bit cases cannot produce a successful scan. If the first pair is $00$, the scan remembers $0$ and continues on the remaining suffix; the induction hypothesis supplies a decomposition there, which prepending $0$ to the doubled word gives the required decomposition of $z$. The condition on the last bit is preserved because the last bit of the enlarged word is the last bit of the remaining word when that word is nonempty, and is the prepended $0$ otherwise. If the first pair is $01$, the scan succeeds immediately with the remaining suffix as $w$; take $u$ empty, and success means precisely that the remembered bit was not $0$. A first pair of $10$ cannot succeed. If it is $11$, the scan remembers $1$ and continues; the induction hypothesis applies, and prepending $1$ gives the decomposition and the corresponding last-bit condition.

Conversely, suppose such a word $u$ gives the stated decomposition. Induct on $u$. If $u$ is empty, the scan sees the separator $01$ immediately and returns $w$, since the condition says the initial remembered bit is not $0$. If $u$ begins with a bit $b$, its doubled form begins with $bb$. For $b=0$ the scan records $0$, and for $b=1$ it records $1$; in either case it consumes that pair and proceeds on the doubled encoding of the rest of $u$, followed by the same separator and suffix. The last-bit condition is exactly the induction hypothesis's condition for this remaining scan, including when the remaining word is empty. Therefore the scan returns $w$.

**Key facts.** `Turing.dbl_nil`, `Turing.dbl_cons`, `Complexity.LogProg.getLast?_cons_of`.
