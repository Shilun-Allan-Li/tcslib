<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.sum_f₂BooleanFunction_eq_card_f₂OneSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Function Sum and Support Cardinality

**Claim.** For a function from the binary cube to $\mathbb F_2$, its sum over all inputs equals, in $\mathbb F_2$, the cardinality of the set of inputs where its value is $1$.

**Proof.** The cardinality of the one-support is the number of inputs for which $f(x)=1$. For each input, its value in $\mathbb F_2$ agrees with the indicator that it equals $1$: if it is zero, both are zero; otherwise, since the only elements of $\mathbb F_2$ are zero and one, it is one. Summing these pointwise equalities identifies the function sum with the natural-number count of the one-support, regarded as an element of $\mathbb F_2$.
