<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDecode_eq_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shape of strings rejected by the pair parser

**Claim.** If the aligned pair parser returns no result on a finite Boolean string $z$, then $z=\mathrm{dbl}(w)\,\tau$ for some finite Boolean strings $w,\tau$, where $\tau$ is empty, has length one, or begins with $10$.

**Proof.** Use induction following the parser's recursive pattern. If $z$ begins with $00$ or $11$, the parser removes that matching pair and recursively parses the remainder. Its failure therefore gives, by induction, a decomposition of the remainder as a doubled string followed by a tail of one of the stated forms. Prefixing the corresponding bit to the doubled string yields the required decomposition of $z$, with the same tail. If $z$ begins with $01$, parsing succeeds immediately, so this case is incompatible with the assumed failure. In the remaining cases, the string has no initial pair handled by these rules, and the parser returns no result directly. Take $w$ empty and $tau=z$. Such a remainder is empty, has one bit, or has at least two bits; in the last case, its first two bits cannot be $00$, $01$, or $11$, since those cases were already handled. They must therefore be $10$, as required.
