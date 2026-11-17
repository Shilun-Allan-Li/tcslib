<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/Arrow.lean :: FABL.univ_ranking3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete rankings of three candidates

**Claim.** For three candidates $a,b,c$, the set of all strict rankings consists exactly of $a>b>c$, $a>c>b$, $b>a>c$, $b>c>a$, $c>a>b$, and $c>b>a$.

**Proof.** Every ranking is one of the six constructors specifying the order of the candidates. Checking these six cases gives exactly the six displayed rankings, and each displayed ranking is one of those cases. Hence the two sets coincide.
