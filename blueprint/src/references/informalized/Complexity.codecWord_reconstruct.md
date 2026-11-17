<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecWord_reconstruct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstructing a Boolean List from Its Code

**Claim.** If a Boolean list $w$ has length $L$ and all entries between $|\alpha|$ and $L-1$ are false, then encoding the function that reads $w$ at the positions assigned to elements of $\alpha$ recovers $w$.

**Proof.** The encoded list and $w$ have the same length: the encoding has length $L$ (`codecWord_length`), and $w$ has length $L$ by hypothesis. It is therefore enough to compare entries at every index $i<L$. If $i<|\alpha|$, the encoding places at index $i$ the value read from $w$ at the corresponding element of $\alpha$; the enumeration and its inverse show that this is exactly the entry of $w$ at $i$. If $i\ge |\alpha|$, the padding hypothesis says that the entry of $w$ at $i$ is false, while the encoding also places false there. Thus the lists agree at every in-range index, and equal lengths then give equality of the lists.

**Key facts.** `Complexity.codecWord_length`.
