<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.TAUTOLOGY_coNPComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tautology Is coNP-Complete

**Claim.** The language of bit strings whose decoded DNF formula is true under every Boolean assignment belongs to coNP, and every language in coNP has a polynomial-time many-one reduction to it.

**Proof.** First, Tautology belongs to coNP ($\texttt{TAUTOLOGY_mem_coNP}$). Now let $L$ be any language in coNP. Its complement $L^c$ is in NP, so the NP-hardness of SAT gives a polynomial-time reduction $f$ from $L^c$ to SAT ($\texttt{SAT_NPHard}$). Map an input $z$ to the serialization of the dual of the decoded CNF formula at $f(z)$. This composite map is polynomial-time computable: the dual-and-serialize map is polynomial-time computable ($\texttt{tautDual_poly}$), and polynomial-time computability is preserved under composition ($\texttt{PolyTimeComputable.comp}$). Decoding the serialization recovers the dual formula ($\texttt{Std.Sat.DNF.decode_serialize}$). The dual is a tautology exactly when the original CNF is unsatisfiable ($\texttt{Std.Sat.CNF.tautology_dual_iff}$). Since $f$ reduces $L^c$ to SAT, unsatisfiability of its output is equivalent to $z\in L$: negating the reduction equivalence gives this, and double negation removes the resulting $\neg\neg(z\in L)$. Thus the constructed map reduces $L$ to Tautology. Together these establish coNP-completeness.

**Key facts.** `Complexity.TAUTOLOGY_mem_coNP`, `Complexity.SAT_NPHard`, `Complexity.tautDual_poly`, `Complexity.PolyTimeComputable.comp`, `Std.Sat.DNF.decode_serialize`, `Std.Sat.CNF.tautology_dual_iff`.
