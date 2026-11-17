<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRight_ne_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Disjoint Embedded Slots

**Claim.** For $i\in\mathrm{Fin}(a)$ and $j\in\mathrm{Fin}(b)$, the position obtained by embedding $j$ after the first $a$ positions differs from the position obtained by embedding $i$ among the first $a$ positions in $\mathrm{Fin}(a+b)$.

**Proof.** The opposite inequality is precisely the previously established disjointness of the two embeddings (`Complexity.clLeft_ne_right`): a position among the first $a$ slots cannot equal one among the final $b$ slots. Reversing the sides of that inequality gives the claimed inequality.

**Key facts.** `Complexity.clLeft_ne_right`.
