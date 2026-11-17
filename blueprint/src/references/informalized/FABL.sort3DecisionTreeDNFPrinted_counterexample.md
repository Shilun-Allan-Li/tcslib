<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.sort3DecisionTreeDNFPrinted_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A decision-tree DNF counterexample

**Claim.** On the input $(-1,-1,1)$, the printed DNF evaluates to $1$, while $\mathrm{Sort}_3$ evaluates to $-1$.

**Proof.** Evaluate both functions at the specified input. The printed DNF’s finite term and literal checks give value $1$; the definition of $\mathrm{Sort}_3$ gives value $-1$. These two computations establish the stated conjunction and exhibit an input on which the functions differ.

**Caveat.** The formal statement proves this evaluation counterexample only; it does not prove the informal statement’s DNF identity, size, or width claims.
