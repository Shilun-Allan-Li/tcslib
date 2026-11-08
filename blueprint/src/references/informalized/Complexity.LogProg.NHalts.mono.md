<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.NHalts.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Halting Bound

**Claim.** If the halting and intermediate-guard conditions hold for length $N$, then they hold for length $N'$ whenever $N\le N'$.

**Proof.** The proof transfers the two clauses separately for an arbitrary choice word of length $N'$. Its terminal-halting clause is retained unchanged. For any intermediate time $t<N'$, the original condition supplies the guard whenever the corresponding configuration is nonhalted, and the implication from $G$ to $G'$ then gives the required $G'$ condition. This proves the stated property for every word of length $N'$.

**Caveat.** The stated source proof passes the halting clause through unchanged and does not use $N\le N'$. As written, this is not justified by the supplied length-$N$ hypothesis when $N'>N$; the proof source appears incomplete or erroneous for the stated monotonicity claim.
