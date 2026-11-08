<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.iterate_absStep_encodeGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iteration of gate decoding

**Claim.** Under the assumption that each gate references only values already available at its position, decoding the encoded gate list for as many steps as there are gates reaches the terminal marker and produces the list obtained by evaluating the gates in order and appending their values.

**Proof.** Proceed by induction on the gate list. For the empty list, the encoded input is already the terminal marker, and no values are added. For a list beginning with a gate $g$, the hypothesis at position $0$ says that $g$'s references lie below the length of the initial values. The encoding of $g$ is parsed back as $g$ (the parsing fact is `parse_encode`), so one decoding step removes its encoding and appends its value. For each remaining gate at position $i$, the original hypothesis at position $i+1$ says its references lie below $|v|+i+1$, which is exactly the length of the updated value list plus $i$. Thus the remaining gates satisfy the induction hypothesis with the updated list. Applying that hypothesis completes the iterations and gives the terminal marker and the ordered evaluation list.

**Key facts.** `Randomized.AlgGate.parse_encode`.
