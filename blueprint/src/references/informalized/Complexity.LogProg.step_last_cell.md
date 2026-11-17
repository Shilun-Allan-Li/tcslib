<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMTime.lean :: Complexity.LogProg.step_last_cell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last Tape Cell After One Step

**Claim.** After one step, the content at any cell on the last work tape is either unchanged or equal to $1$.

**Proof.** If the configuration is already halting, one step leaves it unchanged. Otherwise, let $q$ be its state. The transition hypothesis says that on the last tape the action either makes no write or writes $1$. In the no-write case, the tape function is unchanged everywhere. In the write-$1$ case, the action updates the cell under the tape head to $1$; at any other cell the tape function remains unchanged. Thus at the specified position $z$, its new content is either its previous content or $1$.
