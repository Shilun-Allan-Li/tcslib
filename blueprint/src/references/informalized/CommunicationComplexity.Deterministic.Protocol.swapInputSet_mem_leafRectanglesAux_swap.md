<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.swapInputSet_mem_leafRectanglesAux_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swapping Auxiliary Leaf Rectangles

**Claim.** For any auxiliary leaf rectangle of $p$ relative to $A\times B$, its coordinate swap is an auxiliary leaf rectangle of the role-swapped protocol relative to $B\times A$.

**Proof.** Induct on the protocol, allowing the sets $A$ and $B$ to vary. At an output node, the only rectangle is $A\times B$; its coordinate swap is $B\times A$, as required. At an Alice node, an auxiliary leaf rectangle comes from either the false or true branch, with Alice's set restricted respectively to inputs satisfying $f(x)=\mathrm{false}$ or $f(x)=\mathrm{true}$. After swapping roles, that node is a Bob node, and the same branch restricts the second set by the same condition. The induction hypothesis sends the rectangle from the chosen branch to its coordinate swap in the corresponding branch of the swapped protocol. At a Bob node the argument is symmetric: the original restriction is on $B$, and after swapping roles it is the restriction on the first set. In both cases the branch membership is preserved, proving the claim.
