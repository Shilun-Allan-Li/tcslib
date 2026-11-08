<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.sum_prod_gowersNorm_choice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice-Family Gowers Norm Identity

**Claim.** For functions $f,g:\mathbb F_2^n\to\mathbb R$, summing over all subsets $A$ of $\mathbb F_2^k$ the product, over $s\in\mathbb F_2^k$, of the Gowers $k$-norm of the function chosen at $s$ gives $(\|f\|_{U^k}+\|g\|_{U^k})^{2^k}$.

**Proof.** For a fixed subset $A$, the chosen function is $f$ at indices in $A$ and $g$ at indices in its complement. Its product over all indices therefore factors as the product of $\|f\|_{U^k}$ over $A$ times the product of $\|g\|_{U^k}$ over the complement (the complement-product factorization is `FABL.prod_ite_mem_compl`). Now sum over all subsets $A$. Equivalently, at each index independently choose one of the two summands; distributing the product of these sums yields the original sum. Thus it equals $\prod_{s\in\mathbb F_2^k}(\|f\|_{U^k}+\|g\|_{U^k})$. The cube has $2^k$ elements (`FABL.card_f₂Cube`), so this constant product is the claimed power.

**Key facts.** `FABL.prod_ite_mem_compl`, `FABL.card_f₂Cube`.
