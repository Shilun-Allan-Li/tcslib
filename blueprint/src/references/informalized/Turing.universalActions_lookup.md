<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universalActions_lookup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup in a State Transition Block

**Claim.** For each state and each pair of input and work-tape reads, the transition-action list has nine entries, and the entry indexed by the encoded reads is the machine’s prescribed action.

**Proof.** The action list is formed by taking all three possible input reads and, for each, all three possible work-tape reads. It therefore has $3\cdot3=9$ entries. To identify the requested entry, check the three possibilities for each read: blank, false, and true. Their read indices are respectively $0,1,2$, so the combined index $3r_{\mathrm{in}}+r_{\mathrm{work}}$ selects exactly the pair used to form that list entry. The selected action is consequently the transition prescribed by the machine for those reads.
