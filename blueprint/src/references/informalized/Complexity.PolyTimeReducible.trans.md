<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Reductions.lean :: Complexity.PolyTimeReducible.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Polynomial-Time Reducibility

**Claim.** If $L\le_p L'$ and $L'\le_p L''$, then $L\le_p L''$.

**Proof.** Choose polynomial-time reductions $f$ from $L$ to $L'$ and $g$ from $L'$ to $L''$. Their composition $g\circ f$ is polynomial-time computable, by closure of polynomial-time computability under composition (`Complexity.PolyTimeComputable.comp`). For each input $x$, membership is preserved first from $x$ to $f(x)$ and then from $f(x)$ to $g(f(x))$. Thus $g\circ f$ is a polynomial-time reduction from $L$ to $L''$.

**Key facts.** `Complexity.PolyTimeComputable.comp`.
