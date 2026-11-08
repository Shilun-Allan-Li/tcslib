<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.f₂_add_add_eq_zero_iff_eq_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-term sum criterion

**Claim.** For all $a,b,c\in\mathbb F_2$, $a+b+c=0$ if and only if $c=a+b$.

**Proof.** If $a+b+c=0$, cancellation in the additive group gives $c=-(a+b)$. In characteristic two every element is its own additive inverse, so this is $c=a+b$. Conversely, substituting $c=a+b$ makes the sum $(a+b)+(a+b)$, which is zero because each element added to itself is zero in $\mathbb F_2$.
