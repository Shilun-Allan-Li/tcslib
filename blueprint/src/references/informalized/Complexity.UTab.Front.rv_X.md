<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableauFront.lean :: Complexity.UTab.Front.rv_X -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the First Index

**Claim.** For $a,b,c,e,f\in\mathbb N$, the function $i\mapsto rv(a,b,c,e,f)(i)$ takes the value $a$ at $i=0$.

**Proof.** At index $0$, the defining case for the register assignment returns its first specified value, $a$.
