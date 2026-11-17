<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.mapState_const_inl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Recovery After Constant Renaming

**Claim.** If $d$ has state the left injection of $e$, then mapping every state to $e$ and then injecting back into the left summand recovers $d$.

**Proof.** A configuration’s state is the only component changed by state relabeling. Under the hypothesis, the optional state is the left injection of $e$; the constant map sends its underlying state to $e$, and the left injection sends it back to the original state. Every tape, head position, and output component is unchanged, so the configurations are equal.
