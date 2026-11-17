<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.mem_temps_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Temporary Address Characterization

**Claim.** For natural numbers $k,F$ and integer $a$, $a$ belongs to the set consisting of $c_{\mathrm{ADDR}}=-13$ together with the addresses $c_T(j)=-(23+4j)$ for $k\le j\le 2F$ if and only if either $a=-13$, or $c_T(2F)\le a\le c_T(k)$ and $4$ divides $c_T(0)-a$.

**Proof.** Membership in this set is either the exceptional address $-13$ or an address $a=c_T(j)$ with $k\le j\le 2F$. In the latter case, the explicit formula for $c_T$ gives the two bounds and the required divisibility. Conversely, suppose the bounds and divisibility hold. Then $a$ has the form $-23-4j$ for a natural number $j$; the bounds force $k\le j\le 2F$. Thus $a$ is one of the temporary addresses. The exceptional address case is unchanged on both sides.

**Key facts.** `Set.mem_ofPred_eq`.
