<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.cfgF_inp_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor Input Position Update

**Claim.** Under the stated bit and snapshot hypotheses, the local input-position update rule returns the bit indicating whether the input head is at position $p$ at time $t+1$, together with the presence and value bits of the input-chain value there.

**Proof.** Let $c$ be the configuration at time $t$. The snapshot decoded from the designated field is the snapshot of $c$, and a snapshot is precisely its state, input symbol, and work-tape symbols. The one-step input-head rule (`inp_step`) therefore identifies the rule's head bit with the indicator that the input head of the next configuration is at $p$, using the supplied boundary and neighboring-head bits. The run successor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies this next configuration with the configuration at time $t+1$. For the chain component, `inpChain_eq` says that at position $p$ the chain value is the input symbol at $p$ if the head is there; otherwise it is absent at $p=0$, and otherwise it is the chain value at $p-1$. The designated chain bits give that predecessor value (with no predecessor value at the left boundary), while the input-symbol bits give the value at $p$. Thus the rule's conditional choice between the current input symbol and the predecessor chain is exactly the time-$(t+1)$ chain value at $p$. In each component, encoding an optional Boolean by its presence and defaulted value reproduces its two-bit encoding, yielding the claimed list.

**Key facts.** `Complexity.inp_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.CfgTableau.optOf_isSome_getD`, `Complexity.inpChain_eq`.
