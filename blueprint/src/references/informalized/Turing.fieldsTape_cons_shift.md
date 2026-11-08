<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.fieldsTape_cons_shift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shift of joined fields

**Claim.** For lists $u,v,fs$ and an integer $z\ge -1$, the joined-fields tape for $u,v,fs$ at position $|u|+1+z$ agrees with the joined-fields tape for $v,fs$ at position $z$.

**Proof.** The joined list for $u,v,fs$ is the symbols of $u$, followed by a separator, followed by the joined list for $v,fs$ (`Turing.joinFields_cons_cons`). If $z\ge0$, the queried position lies in that final joined-list portion, at its position $z$; indexing past the prefix of length $|u|+1$ therefore gives the same tape symbol. If $-1\le z<0$, then, since $z$ is an integer, $z=-1$. The shifted position is the final cell of the prefix, namely the separator after $u$, while the tape at position $-1$ on the right is blank by definition. Thus both sides are blank.

**Key facts.** `Turing.joinFields_cons_cons`.
