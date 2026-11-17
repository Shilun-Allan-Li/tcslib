<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Randomized.attemptBit_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing a successful output bit

**Claim.** The attempt on input $x$ with choice string $u$ returns $v$ exactly when the run halts and outputs the one-bit string $v$.

**Proof.** Split according to whether the halt-run record is absent or present. If it is absent, the run has not halted (`Turing.FinNDTM.haltRun_eq_none_iff`), and binding the absent option cannot produce a bit; conversely, a halted run is incompatible with this case. If the record is present, it records both that the run halted and the run’s output (`Turing.FinNDTM.haltRun_eq_some_iff`). The remaining condition is that the output list maps to the bit $v$ under the single-bit-output decoder. By its definition, this happens exactly when the output list is $[v]$; lists of any other length cannot decode to $v$. Combining the two conditions proves the equivalence.

**Key facts.** `Turing.FinNDTM.haltRun_eq_none_iff`, `Turing.FinNDTM.haltRun_eq_some_iff`.
