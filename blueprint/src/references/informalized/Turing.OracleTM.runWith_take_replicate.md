<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleTM.runWith_take_replicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Replicated Choices Match Deterministic Running

**Claim.** When $s\le t$, running the nondeterministic machine on the first $s$ bits of $t$ false bits gives the same configuration as running the deterministic oracle machine for $s$ steps.

**Proof.** The first $s$ entries of a length-$t$ list of false bits are precisely the length-$\min(s,t)$ list of false bits; since $s\le t$, this is a length-$s$ list. The correspondence between the nondeterministic machine obtained from $M$ and the deterministic machine states that running on any choice list $w$ gives the deterministic run for $|w|$ steps (`Turing.OracleTM.toOracleNDTM_runWith`). Apply it to the length-$s$ false list. Its length is $s$, so the resulting deterministic run is exactly the one claimed.

**Key facts.** `Turing.OracleTM.toOracleNDTM_runWith`.
