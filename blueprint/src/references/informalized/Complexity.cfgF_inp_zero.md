<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.cfgF_inp_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Input Position Update

**Claim.** Under the stated initial-row bit hypotheses, the local input-position update rule returns the indicator that the time-zero input head is at $p$, followed by the presence and value bits of the time-zero input-chain value at $p$.

**Proof.** At time zero the configuration is the initialized configuration, whose shifted input-head position is $1`; this follows from `Turing.MultiTapeTM.runFrom_zero` and the initial-configuration definition. The first-bit hypothesis selects the initial branch of the local rule, and the second-bit hypothesis supplies exactly the indicator that $p=1$. The input-symbol and predecessor-chain bits reconstruct their respective optional Boolean values, since presence together with the defaulted value encodes an option (`Complexity.CfgTableau.optOf_isSome_getD`). Now apply `inpChain_eq`: if the head position $1$ equals $p$, the chain value is the input bit at $p$; otherwise it is absent when $p=0$, and for positive $p$ it is inherited from $p-1$. Splitting into $p=1$ and $p\ne1$ makes the head indicator and this chain recurrence agree with the rule's output, proving the stated encoding.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Complexity.CfgTableau.optOf_isSome_getD`, `Complexity.inpChain_eq`.
