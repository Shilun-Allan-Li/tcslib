<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.swapInputSet_swapInputSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Swap Is an Involution

**Claim.** Swapping the coordinates of every element of a set $R\subseteq X\times Y$ twice returns $R$.

**Proof.** To prove equality of the two sets, test an arbitrary pair $(x,y)$. It belongs to the twice-swapped set exactly when $(y,x)$ belongs to the once-swapped set, which holds exactly when $(x,y)\in R$. Thus the sets have the same elements.
