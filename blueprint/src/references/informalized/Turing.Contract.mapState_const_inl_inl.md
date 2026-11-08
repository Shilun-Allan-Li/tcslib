<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.mapState_const_inl_inl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery After State Relabeling

**Claim.** When $d$ has state the left-left injection of $e$, mapping its states constantly to $e$ and then applying the two left injections recovers $d$.

**Proof.** State relabeling changes only the state component. The given state is the left-left injection of $e$; the constant map sends it to $e$, and the two left injections return it to the original state. All other configuration components remain unchanged, so the resulting configuration equals $d$.
