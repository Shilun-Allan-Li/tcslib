<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.record_tag_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct State Tags

**Claim.** If $i$ differs from the first component of a dependent-sum state $v$, then a configuration whose states are in phase $i$, after tagging its states by $i$, cannot have state $v$.

**Proof.** If the configuration is halted, its state is none and so cannot equal the specified tagged state. Otherwise write its state as some $s$. Equality of the tagged state $(i,s)$ with $v$ would imply equality of their first components, hence $i=v.1$, contradicting the hypothesis.
