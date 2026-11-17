<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalDimensionError_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dimension error factorization

**Claim.** For every natural number $w$, the critical dimension error is $w$ times the critical size error.

**Proof.** By definition, the critical dimension is the critical size multiplied by $w$. Substituting this and the two error definitions, the claimed equality reduces to expanding $w\bigl((\log 2)2^w-s\bigr)$ and regrouping terms; both sides are $(\log 2)w2^w-ws$.
