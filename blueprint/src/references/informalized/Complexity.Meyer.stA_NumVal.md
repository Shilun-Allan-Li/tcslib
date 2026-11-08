<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.stA_NumVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Answers Under Numerical Encoding

**Claim.** Under the numerical encoding, the state-answer atom for a state-and-output-register pair at time coordinate $T$ and index $0$ equals the corresponding value of $\mathrm{Ans}$, with the time specified by $T$.

**Proof.** Unfolding the state-answer query selects precisely the atom indexed by that state-and-output-register pair, time coordinate $T$, and index coordinate $a_0$. The numerical encoding sends these coordinates to $\mathrm{tvOf}(W,t,T)$ and $\mathrm{avOf}(a,j,a_0)=0$, respectively. Thus the value is $\mathrm{Ans}(\mathrm{st}(\sigma),\mathrm{tvOf}(W,t,T),0)$, as asserted.
