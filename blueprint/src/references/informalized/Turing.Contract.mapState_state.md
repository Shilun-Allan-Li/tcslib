<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean :: Turing.Contract.mapState_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State After Relabeling

**Claim.** For every configuration $c$ and function $f$ between state sets, the state of the relabeled configuration is the image of the original optional state under $f$.

**Proof.** By definition, relabeling replaces the state component $c.state$ by its image under the optional map induced by $f$ and leaves the other components unchanged. Therefore the relabeled configuration has state $c.state.map f$.
