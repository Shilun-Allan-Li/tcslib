<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fknOptimalityFunction_toReal_cons_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive First-Coordinate Value

**Claim.** For every $q\in\mathbb{N}$ and every sign vector $x$ of the associated tail dimension, the real-valued constructed Boolean function at the vector with first coordinate $1$ and tail $x$ equals $1$.

**Proof.** At the input formed by adjoining the coordinate $1$ to $x$, the function returns $1$ whenever the small-set indicator equals $1$, and otherwise returns the first input coordinate. In the first case its value is already $1$; in the second case that first coordinate is $1$. Thus the Boolean function has value $1$ in either case, and converting its sign value to a real leaves that value unchanged.
