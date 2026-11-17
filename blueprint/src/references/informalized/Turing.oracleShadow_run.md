<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleShadow_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oracle shadow simulation over a run

**Claim.** If the selected tape head initially lies on the side of the origin indicated by $b$, then after any $t$ steps there is a tag describing the side of its new position, and the augmented machine's run equals the augmentation of the original run with that tag.

**Proof.** Track the original and shadow configurations together. Use the invariant that the shadow configuration is the augmentation of the original one with some tag, and that this tag correctly describes the selected head's side of the origin. The initial pair satisfies the invariant by the assumed side condition. If it holds at one time, the one-step shadow simulation (`oracleShadow_step`) supplies a new tag for which both the side condition and the configuration equality hold after one more step. Induction therefore establishes the invariant after $t$ steps. The two coordinates of the iterated paired transition are exactly the $t$-step runs of the original and shadow machines, respectively, so the invariant yields the desired tag and equality.

**Key facts.** `Turing.oracleShadow_step`.
