<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_cleared_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending the Erased Interval

**Claim.** Updating the tape obtained by erasing the first $j$ cells of $[\ell,\infty)$ to be blank at cell $\ell+j$ gives the tape obtained by erasing the first $j+1$ cells.

**Proof.** Compare the two tapes at an arbitrary cell $z$. If $z=\ell+j$, the update makes that cell blank, and it belongs to the interval $[\ell,\ell+j+1)$, so the extended erasure is blank there as well. Otherwise, the update leaves the tape unchanged at $z$. In this case, the conditions $\ell\le z$ and $z<\ell+j$ are equivalent to $\ell\le z$ and $z<\ell+(j+1)$: the only newly included integer endpoint is $\ell+j$. Thus both tapes agree at every cell.
