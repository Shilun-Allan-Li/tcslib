<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityNextActualAssignment_tree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Parity Assignment Identity

**Claim.** For natural numbers $n,r,t,q$, a sign vector $x$ of length $n$, and a position $g$ in $	ext{Fin}(r^q)$, the assignment obtained by taking the product of the depth-$t$ tree values at each child of $g$ equals the depth-$(t+1)$ parity tree assignment at $g$.

**Proof.** To prove equality of the two parity block assignments, compare their values at an arbitrary child index $j\in\text{Fin}(r)$. The left side takes the product of the depth-$t$ tree assignment at the child group indexed by $(g,j)$. The child-group coordinate formula, $(g,j)\mapsto g r+j$, identifies this with the product of the depth-$t$ tree values at indices $g r+j$. By the recursive definition of the parity tree at depth $t+1$, this product is precisely its value at $g$ and child index $j$. Since the assignments agree at every $j$, they are equal.

**Key facts.** `FABL.parityChildGroup_val`.
