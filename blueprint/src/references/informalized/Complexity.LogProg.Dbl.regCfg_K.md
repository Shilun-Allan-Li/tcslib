<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/DblLang.lean :: Complexity.LogProg.Dbl.regCfg_K -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Update of a Represented Configuration

**Claim.** Replacing the represented configuration's register tape with the binary representation of $v'$ and moving its work-tape head to $q$ yields the represented configuration with state $s$, input-head position $ip$, value $v'$, and head position $q$.

**Proof.** Both configurations have state $s$, input-head position $ip$, and empty output. Each has one register, so the register update replaces its tape by the buffer tape for the binary representation of $v'$ and sets its head position to $q$. Thus their tape and head-position functions also agree, giving equality of configurations.
