<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_update_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Word Update

**Claim.** When $k>0$, updating the first width-bank position in the host layout for $(s,u,v)$ with $a$ gives the host layout for $(s,a,v)$.

**Proof.** Compare the layouts at an arbitrary tape index. The distinguished initial position is unchanged by the update, so both layouts contain $s$ there. In the width bank, the first position corresponds to index $0$ of that bank; its word changes from $u$ to $a$. Every later width-bank position is unchanged, since the standard assignment places the width word only at bank index $0$ and is empty at all other indices. The suffix bank is disjoint from the width-bank position being updated and is unchanged. Therefore the layouts agree at every index. The condition $k>0$ ensures that the first width-bank position exists.
