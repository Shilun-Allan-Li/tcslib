<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Zone.lean :: Turing.zoneStageWord_getElem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of the Encoded Zone Word

**Claim.** At position $p$, the encoded word contains the corresponding entry from position $\lfloor p/2\rfloor$ of the original list, using the first or second Boolean of its pair according as $p$ is even or odd.

**Proof.** Induct on the list, with the position arbitrary. The empty list gives no entry. For a nonempty list, positions zero and one are the two Boolean entries encoding its first optional value, and checking the two encoding orders gives the claimed even/odd rule. For any later position, write it as $p+2$; its pair index is one more than the pair index for $p$, while its parity is the same. The induction hypothesis applied to the tail therefore gives the required entry and encoding choice.
