<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Select_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Selection of Polynomial-Time Functions

**Claim.** Selecting from a finite list of polynomial-time word functions using a polynomial-time computable unary index, and returning the empty word when the index is out of range, defines a polynomial-time computable function.

**Proof.** Induct on the list. For the empty list, selection always returns the empty word, a constant polynomial-time function (`Complexity.clA5_pt_const`). For a list with head function $f$ and tail, first form the tail selector using index $v(z)-1$. The unary representation of this predecessor is polynomial-time computable: subtract one from the unary index (`Complexity.clA5Sub_native`), using the polynomial-time unary constant one. By induction the tail selector is polynomial-time computable. The test whether $v(z)=0$ is polynomial-time computable from the index (`Complexity.clA5_pt_eq`). Use this test to choose the empty word when the index is zero, and otherwise choose $f(z)$ at index zero of the tail selector; conditional choice preserves polynomial-time computability (`Complexity.clA5_pt_cond`). The head function is polynomial-time computable by the hypothesis on the list. When $v(z)=0$, list lookup returns $f(z)$; when $v(z)>0$, lookup in the tail at index $v(z)-1$ gives the same selected value, including the empty-word default when the original index is out of range. This is the desired selector.

**Key facts.** `Complexity.clA5_pt_const`, `Complexity.clA5Sub_native`, `Complexity.clA5_pt_eq`, `Complexity.clA5_pt_cond`.
