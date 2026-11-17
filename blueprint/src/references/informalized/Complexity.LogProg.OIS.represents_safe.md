<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.represents_safe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety of Represented Configurations

**Claim.** If a compiled configuration represents a configuration of the machine whose work-tape heads lie in $[-S,S]$, then the compiled configuration satisfies the safety bounds for input length $|v|$ and parameter $S$.

**Proof.** Unpack the representation: there is a counter value $i\le |v|$ such that the compiled configuration is the image of the original configuration with counter $i$ and the specified phase. The image safety lemma (`Complexity.LogProg.OIS.imageCfg_safe`) says precisely that this image satisfies the required bounds whenever $i\le |v|$ and the original work-tape heads lie in $[-S,S]$. Applying it proves the claim.

**Key facts.** `Complexity.LogProg.OIS.imageCfg_safe`.
