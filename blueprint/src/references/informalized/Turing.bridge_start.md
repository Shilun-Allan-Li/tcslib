<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup of the Bridging Machine

**Claim.** From its initial configuration on the embedded Boolean input, the bridging machine reaches the configuration at input-head position $0$ with empty output, the input’s stack word on the main stack, and empty other stacks, in the execution state for the translated initial statement with empty register.

**Proof.** Concatenate three reachable segments. First, the forward scan lemma reaches the scanning configuration at position $|x|+1$ after $|x|$ steps (`bridge_scan`). Next, the seeding lemma takes three steps to the backward-reading state at position $|x|$, with the sentinel and terminator on the main stack (`bridge_seed`). Finally, apply the backward-reading lemma at $j=|x|$; it reconstructs the input stack word and reaches the execution configuration for the translated initial statement, with head position $0$ and empty register. Transitivity of reachability composes these segments (`bridgeReach_trans`), and the resulting stack word is the full input word because dropping $|x|$ entries from $x$ leaves the empty list (`bridge_back`).

**Key facts.** `Turing.bridgeReach_trans`, `Turing.bridge_scan`, `Turing.bridge_seed`, `Turing.bridge_back`.
