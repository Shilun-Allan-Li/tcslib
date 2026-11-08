<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.temps_subset_scratch -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Temporary addresses lie in scratch space

**Claim.** For natural numbers $k$ and $F$, every temporary address indexed from $k$ through $2F$, together with the address $c_{\mathrm{ADDR}}$, belongs to the scratch set consisting of the four designated scratch addresses and all temporary addresses indexed from $0$ through $2F$.

**Proof.** Take an address in the set of temporary addresses indexed from $k$. By definition, it is either $c_{\mathrm{ADDR}}$ or equals $c_T(j)$ for some $j$ with $k\le j\le 2F$. In the first case it belongs to the temporary set indexed from $0$, which is included in the scratch set. In the second case, $0\le k\le j\le 2F$, so the same address belongs to the temporary set indexed from $0$ and hence to the scratch set. The scratch set also includes the designated addresses, completing the inclusion.

**Caveat.** The supplied proof source is only the placeholder `by cells`, so it does not reveal the actual proof route. The account follows directly from the stated definitions.
