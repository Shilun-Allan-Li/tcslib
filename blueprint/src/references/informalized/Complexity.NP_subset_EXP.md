<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.NP_subset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Is Contained in Exponential Time

**Claim.** Every language in NP belongs to EXP; that is, $\mathrm{NP}\subseteq\mathrm{EXP}$.

**Proof.** Let $L\in\mathrm{NP}$, witnessed by a polynomial-time verifier $V$ and certificates of length $C(n+1)^c$. The polynomial-time characterization of P supplies a deterministic machine for $V$ with time bound $a(n+1)^d$ (`mem_P_iff`). The projection-decider construction decides whether an input has a certificate of the prescribed length accepted by $V`; its running time consists of enumerating the $2^{C(n+1)^c}$ possible certificates and checking them, together with polynomial overhead (`exists_proj_decider`). By the defining certificate property, this projected language is exactly $L$.

The proof then bounds the running time explicitly. Writing $X=n+C(n+1)^c+1$, both $X^d$ and $X^{c+1}$ are at most $X^{d+c+1}$, so the projection bound is at most $b(a+1)2^{C(n+1)^c}X^{d+c+1}$. The exponential-budget estimate absorbs this polynomial factor into a bound $A2^{n^e}$ for suitable constants (`enumBudget_bound`). Thus the resulting deterministic decider witnesses membership in one of the time classes whose union is EXP.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.exists_proj_decider`, `Complexity.enumBudget_bound`.
