<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.LogProg.vword_whole₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Whole Input with Two Registers

**Claim.** In whole-input mode, the virtual word built from input $u$ and registers $r,s$ is the encoding of $u$ paired with the encoding of $(V(r),V(s))$.

**Proof.** Whole-input mode renders the first segment as the doubling of $u$. Since there are two arguments, their segments are both marked doubled: they render as the doubling of $V(r)$ and the doubling of $V(s)$. The virtual-word construction inserts the separator $(0,1)$ between each successive pair of rendered segments. Applying `pairEncode_eq_dbl` first to the two argument words identifies their concatenation as the encoding of $(V(r),V(s))$; applying it to the doubled input followed by that encoded argument identifies the entire word as the encoding of $u$ with that second component.

**Key facts.** `Turing.pairEncode_eq_dbl`.
