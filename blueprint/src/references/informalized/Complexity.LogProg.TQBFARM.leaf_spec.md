<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.leaf_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base Case for the Formula Specification

**Claim.** If $x$ encodes the quantifier string $q$ followed by the serialization of the CNF formula $\varphi$, and the stated register and input bounds hold, then the machine runs from the node at depth $|q|$ to the return state reporting whether $\varphi$ evaluates to true under the corresponding assignment.

**Proof.** Fix an assignment register $S<2^{|q|+1}$ and put $M=|q|$. The node routine first reaches the state that reads input position $2M$ (`node_run`). The encoding has a false separator at that position, so the machine takes the negative branch to `nd2`; after advancing the pointer, it reads the true bit at position $2M+1$ and takes the branch to `leaf`. These bit values follow from the encoding’s indexed-bit description (`getD_enc`), and the length formula for the encoding (`length_enc`) ensures those positions lie within the input. The intermediate register updates preserve the guard by the stated bounds. From `leaf`, the formula serialization begins at the next position: unfolding the pair encoding identifies the remaining suffix with the serialization of $\varphi$. The formula-processing run (`formula_run`) therefore returns to the root with the value $\mathrm{CNF.eval}(\mathrm{asg}(M,S),\varphi)$. Finally, the leaf characterization of the quantified-formula value (`val_leaf`) identifies this Boolean with $\mathrm{Val}(q,\varphi,M,S)$. Concatenating these guarded runs and identifying the final states proves the required call specification.

**Key facts.** `Complexity.LogProg.TQBFARM.node_run`, `Complexity.LogProg.TQBFARM.read_f`, `Complexity.LogProg.TQBFARM.getD_enc`, `Complexity.LogProg.TQBFARM.read_t`, `Complexity.LogProg.TQBFARM.formula_run`, `Complexity.LogProg.TQBFARM.val_leaf`, `Complexity.LogProg.AReach.trans`.
