<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleAgreement.lean :: Turing.OracleNDTM.runWith_eq_of_agree_length_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Under Short-Query Oracle Agreement

**Claim.** If $O$ and $O'$ agree on membership for every word of length less than $|w|$, then running on $w$ from the initial configuration on $x$ yields the same final configuration with either oracle.

**Proof.** Use the prefix-agreement result (`Turing.OracleTM.runWith_take_eq_of_agree`). To meet its hypothesis at each prefix length $s<|w|$, consider the query made after running on $w.take(s)$. Its length is at most $|w.take(s)|$ by the query-length bound (`Turing.OracleNDTM.queryString_runWith_length_le`), and this is at most $s$, hence strictly less than $|w|$. The assumed oracle agreement therefore applies to this query whenever the run is in its query state. The prefix-agreement result now gives equality of the two configurations for every prefix length up to $|w|$. Taking the full-length prefix, which is $w$, gives the claimed equality.

**Key facts.** `Turing.OracleNDTM.queryString_runWith_length_le`, `Turing.OracleTM.runWith_take_eq_of_agree`.
