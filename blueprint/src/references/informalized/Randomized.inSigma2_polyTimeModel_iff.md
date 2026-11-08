<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.inSigma2_polyTimeModel_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-level polynomial hierarchy characterization

**Claim.** A language belongs to the two-witness class defined by an efficient predicate and polynomially bounded witness lengths exactly when it belongs to $\Sigma_2^P$, equivalently when membership has an existential polynomial-length witness followed by a universal polynomial-length witness checked by a polynomial-time language.

**Proof.** Suppose first that $L$ has an efficient two-witness predicate $N$ and witness bounds $a_1(|x|+1)^{k_1}$ and $a_2(|x|+1)^{k_2}$. Efficiency supplies a polynomial-time language $V$ recognizing the encoded triples: $N(x,u,v)$ is true exactly when $\langle\langle x,u\rangle,v\rangle$ belongs to $V$. Each witness-length function is polynomial-time unary, by the polynomial-length fact (`Complexity.PolyHierarchy.unaryPT_poly`) applied to the identity map (`Complexity.polyTimeComputable_id`). The normal-form characterization of the alternating hierarchy (`Complexity.PolyHierarchy.mem_altClass_of_normal`) then places the language described by an existential quantifier over $u$ and a universal quantifier over $v$ in the second alternating class. The defining equivalence for $L$ identifies it with that language, so $L\in\Sigma_2^P$.

Conversely, the two-quantifier characterization of $\Sigma_2^P$ (`Complexity.mem_SigmaP_two_iff_exists_forall`) gives a polynomial-time language $V$ and one common polynomial bound $C(|x|+1)^c$ for both witnesses, such that membership is equivalent to the stated existential-universal condition. Define $N(x,u,v)$ to test whether the encoded triple belongs to $V$. This predicate is efficient by the definition of the two-witness model, and its acceptance condition is precisely membership in $V$. The characterization therefore supplies the required two-witness representation of $L$.

**Key facts.** `Complexity.PolyHierarchy.unaryPT_poly`, `Complexity.polyTimeComputable_id`, `Complexity.PolyHierarchy.mem_altClass_of_normal`, `Complexity.mem_SigmaP_two_iff_exists_forall`.
