<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.index_inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safe Increment of the Encoded Index

**Claim.** From the increment phase with index $i<|v|$, the compiled program reaches the query phase with index $i+1$ after finitely many steps, and every earlier configuration satisfies the safety bounds.

**Proof.** Apply the increment-routine theorem `inc_run` to the extra tape, which initially stores $\operatorname{bits}(i)$ at position zero. The routine reaches the same tape with $\operatorname{bits}(i+1)$ at zero, and its intermediate states are restricted to the two non-call increment phases; its head stays between $-1$ and $|\operatorname{bits}(i+1)|$. By `index_view`, the initial and final register configurations are the encoded configurations, with the endpoint in the query phase and index $i+1$. Each intermediate configuration is safe by `index_fragment_safe`: the original heads retain their bounds, the routine's states have no oracle call, and the extra head has the required lower bound. For the upper bound, $i+1\le |v|+1$, so monotonicity of binary-expansion length (`length_bits_mono`) gives $|\operatorname{bits}(i+1)|\le |\operatorname{bits}(|v|+1)|$.

**Key facts.** `Complexity.LogProg.inc_run`, `Complexity.LogProg.OIS.index_view`, `Complexity.LogProg.OIS.index_fragment_safe`, `Complexity.LogProg.length_bits_mono`.
