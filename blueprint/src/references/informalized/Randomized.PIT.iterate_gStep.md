<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.iterate_gStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of the gate-evaluation machine

**Claim.** After any number $T$ of steps, the encoded machine state with fixed context and data $(w,vs)$ is the encoding of the same context and the pair obtained by iterating the abstract decoding-and-evaluation step $T$ times, with modulus $\operatorname{val}(R)+1$ and assignment $i\mapsto\operatorname{val}(P_i)+1$.

**Proof.** Induct on $T$. At zero steps, both sides are the original encoded state. For the successor step, apply the machine once to the encoded state. The one-step correspondence says that this is the encoding of the abstract work-state after one abstract step (`gStep_encState`); that abstract step is exactly `absStep` (`wStep_eq_absStep`). Now apply the induction hypothesis to the resulting abstract state for the remaining $T$ steps. The resulting encoding is precisely the state obtained by iterating the abstract step $T+1$ times.

**Key facts.** `Randomized.PIT.gStep_encState`, `Randomized.PIT.wStep_eq_absStep`.
