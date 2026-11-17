<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.xCfg_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Symbol After Configuration Update

**Claim.** After the configuration update, work tape $r$ reads the content that the original tape $r$ has at position $p$.

**Proof.** The update preserves all work-tape contents and sets the head position of tape $r$ to $p$. The symbol read on a tape is its content at that tape's head position. Thus the updated tape reads the original tape $r$ at position $p$.
