<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.clockTape_zipper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Captured Clock Tape as a Zipper

**Claim.** For every bit word $w$, its captured clock tape equals the tape formed by a zipper with frontier at coordinate $1$, left list consisting of the origin marker, and right list consisting of the symbols of $w$ encoded as bit symbols.

**Proof.** Compare the two tapes at an arbitrary integer coordinate $z$. At $z=0$, the captured tape gives the origin marker, and the zipper's left list selects that same marker. Now suppose $z\ne0$. If $z<1$, then the buffer coordinate $z-1$ is negative, so the captured tape is blank. The zipper looks to the left of its frontier; its requested index in the one-element left list is at least $1$, so that lookup is blank as well. If instead $z\ge1$, the captured tape reads the word at index $z-1$, while the zipper reads the right list at index $z-1$. Those entries agree because the right list is exactly the word with each bit encoded as its corresponding bit symbol; when the index is beyond the word, both are blank. Thus the tapes agree at every coordinate.
