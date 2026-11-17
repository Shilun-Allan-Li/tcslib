<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_advance_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Candidate-Advance Configuration

**Claim.** At count zero, the cleanup scan configuration with candidate input $w$ and candidate word $s$ equals the canonical seam configuration with state $(0,\mathrm{false})$ and work tape storing $s$.

**Proof.** At count zero, the scan state is $(0,\mathrm{false})$, the input-head position is one, and the output is empty. The scratch tape is blank because its defining interval condition cannot hold when its lower endpoint is zero and its upper endpoint is zero. The remaining work tape is the buffer for $s$, and both head positions are zero. These are exactly the fields of the canonical configuration with one work tape storing $s$.
