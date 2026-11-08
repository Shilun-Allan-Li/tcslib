<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Replacement.lean :: BooleanAnalysis.GaussianSpace.independent_affine_replacement_bound_c3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent Affine Replacement Bound

**Claim.** Under the stated moment, independence, smoothness, and integrability assumptions, the difference between the two expectations is bounded by the product of the third-moment sum of $U,V$ and the third moment of $D$, multiplied by $C/6$.

**Proof.** Set $K=(C/6)(\mathbb E|U|^3+\mathbb E|V|^3)$. Since $D\in L^3$, the function $|D|^3$ is integrable, so the comparison bound can be applied with the weight $(a,d)\mapsto K|d|^3$. Independence of each replacement variable from $(A,D)$ lets us compare the original expectations by integrating the corresponding scalar comparison over the joint values $(a,d)$. For each fixed $a,d$, the third-order affine replacement estimate (\texttt{affine_replacement_bound_c3}) bounds the scalar difference by $(C/6)|d|^3(\mathbb E|U|^3+\mathbb E|V|^3)$; its hypotheses are exactly the matching first and second moments, the $L^3$ assumptions, and the bound on the third derivative. This is $K|d|^3$. Integrating this pointwise estimate through the independent affine comparison bound (\texttt{independent_affine_comparison_bound}) gives $K\mathbb E|D|^3$, which is the asserted bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.affine_replacement_bound_c3`, `BooleanAnalysis.GaussianSpace.independent_affine_comparison_bound`.
