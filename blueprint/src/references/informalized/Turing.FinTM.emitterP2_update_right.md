<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_update_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix-Length Word Update

**Claim.** When $l>0$, updating the first suffix-length-bank position in the host layout for $(s,u,v)$ with $a$ gives the host layout for $(s,u,a)$.

**Proof.** Evaluate both layouts at an arbitrary tape index. The initial position is unchanged. Every width-bank position is also unchanged, since the updated position belongs to the suffix bank. Within that bank, the index corresponding to bank index $0$ changes from $v$ to $a$; all later positions retain their empty words. The banks occupy disjoint positions, so the layouts agree everywhere. The assumption $l>0$ guarantees that the designated suffix-bank position exists.
