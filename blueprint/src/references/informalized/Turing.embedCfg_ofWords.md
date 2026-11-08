<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean :: Turing.embedCfg_ofWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding Word Configurations

**Claim.** If $m\le k$, embedding the configuration built from state $q$ and words $w$ gives the configuration in state $\mathrm{inject}(q)$ whose first $m$ tapes have the corresponding words and whose remaining tapes are blank.

**Proof.** Unfold the two constructions and compare the configuration fields. The state and input-head position agree directly, as does the output. For each of the $k$ tape indices, split according to whether its index is less than $m$. In the first case, both configurations use the corresponding word $w_i$ and head position $0$; in the second, the embedded tape is blank and its corresponding word is empty, so its buffer tape is blank, and the head position is again $0$. Thus every field agrees.
