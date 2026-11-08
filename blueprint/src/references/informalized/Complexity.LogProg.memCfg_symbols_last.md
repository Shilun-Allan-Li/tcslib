<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.memCfg_symbols_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symbol under the added tape head

**Claim.** In the configuration obtained by adjoining a tape with contents $M$ and head position $p$, the symbol under that added tape's head is $M(p)$.

**Proof.** The added tape is placed in the final slot of the enlarged tape family, with contents $M$ and head position $p$. Evaluating its contents at that head position gives $M(p)$.
