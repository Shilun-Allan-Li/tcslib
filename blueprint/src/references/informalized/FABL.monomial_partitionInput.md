<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PolynomialThresholdUniformStability.lean :: FABL.monomial_partitionInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monomial on a Partitioned Input

**Claim.** The monomial on the coordinatewise product input factors as the monomial on $z$ times the monomial on $w$ indexed by output coordinates hit an odd number of times by $S$.

**Proof.** First use multiplicativity of sign value to split each factor $\operatorname{signValue}(z_iw_{\pi(i)})$ into $\operatorname{signValue}(z_i)\operatorname{signValue}(w_{\pi(i)})$. The product over $S$ therefore separates into the monomial on $z$ and the product of the pulled-back $w$ factors. Group the latter factors by their output coordinate $j$. If the fiber over $j$ contains an even number of indices from $S$, its repeated sign factor cancels in pairs and contributes $1$; if it contains an odd number, it contributes $\operatorname{signValue}(w_j)$. This parity computation is precisely the fiber sign product identity (`fiberSignProduct_eq_ite_odd`). Multiplying over $j$ leaves exactly the monomial indexed by the output coordinates with odd fiber cardinality.

**Key facts.** `FABL.fiberSignProduct_eq_ite_odd`.
