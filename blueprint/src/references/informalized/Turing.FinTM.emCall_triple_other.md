<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_triple_other -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple selection isolates its tape

**Claim.** For source tapes $i,j$ and a component $r$, selection for tape $i$ at the physical index assigned to component $r$ of tape $j$ returns $r$ when $j=i$, and is undefined otherwise.

**Proof.** Split on whether $j=i$. If they are equal, the assertion is exactly the inverse property for a tape's own component index (`emCall_triple_inverse`). If they differ, their finite indices have different numerical values. For each of the three component choices, the physical index assigned to $j$ therefore matches none of the three indices tested by selection for $i$, so selection is undefined.

**Key facts.** `Turing.FinTM.emCall_triple_inverse`.
