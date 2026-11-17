<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_vhost_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding the virtual host

**Claim.** Starting from the virtual host of a start configuration, the virtual-host simulation reaches the corresponding halting configuration with input-head position 1 in at most the original input-head position plus 2 steps, with its buffer head at the origin and its buffer tape storing the input word.

**Proof.** Apply the rewind-run lemma to the zero-work-tape machine: within the stated time bound, the machine halts with input-head position 1, and its work-tape head positions have not changed. The virtual-host simulation lemma then supplies a tag for which its configuration at that same time is exactly the virtual host of the simulated configuration, with the chosen input position and output prefix preserved. Rewriting the simulated configuration using the rewind-run conclusion identifies it with the required halting configuration. Finally, the virtual-host buffer head is at the original input-head position minus 1; since that head position is now 1, its location is 0. By the definition of the virtual-host configuration, the buffer tape still stores the input word.

**Key facts.** `Complexity.b2b_rewind_run`, `Turing.vhostEmitTM_runFrom`.
