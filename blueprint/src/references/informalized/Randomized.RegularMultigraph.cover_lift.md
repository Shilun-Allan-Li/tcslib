<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.cover_lift -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a walk to the two-sheeted graph

**Claim.** For a finite sequence of neighbor steps from $v$ to $w$, there is a Boolean parity such that, from either starting label $b$, the lifted walk goes from $(v,b)$ to $(w,b\mathbin{\mathrm{xor}}\pi)$.

**Proof.** Induct on the sequence of neighbor steps. For the empty sequence, take parity to be false: the lifted walk stays at $(v,b)$, and exclusive-or with false leaves $b$ unchanged. For the induction step, suppose the existing walk has parity $\pi$ and append a neighbor step from $x$ to $y$. Set the new parity to $\neg\pi$. By the induction hypothesis, the lifted walk reaches $(x,b\mathbin{\mathrm{xor}}\pi)$. The appended lifted edge changes that label to its complement. For Boolean labels, complementing $b\mathbin{\mathrm{xor}}\pi$ gives $b\mathbin{\mathrm{xor}}\neg\pi$, so the extended walk has the claimed endpoint for every starting label.
