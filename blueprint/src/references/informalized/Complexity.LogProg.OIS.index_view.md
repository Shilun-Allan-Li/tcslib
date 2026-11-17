<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.index_view -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replacing the Encoded Index Tape

**Claim.** Replacing the extra tape and its head position in the encoded configuration by the tape holding $\operatorname{bits}(j)$ at position zero, and changing the phase to $\mathrm{ph}'$, produces exactly the encoding with index $j$ and phase $\mathrm{ph}'$.

**Proof.** Compare the configuration fields. The state of the original configuration is $s$, so setting the encoded state to $(s,\mathrm{ph}')$ agrees with encoding that same state in phase $\mathrm{ph}'$. The input head and output are unchanged. For every original tape, the tape contents and head position are unchanged by the register replacement; for the extra tape, the replacement supplies exactly the buffer tape for $\operatorname{bits}(j)$ and head position zero. These fieldwise equalities establish equality of the configurations.
