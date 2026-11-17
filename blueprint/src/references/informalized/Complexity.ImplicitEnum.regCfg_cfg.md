<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.regCfg_cfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Configuration Update

**Claim.** Updating register $0$ of the enumerator configuration to state $s'$, the tape containing the bits of $n$, and head position zero gives the configuration with counter $n$.

**Proof.** The update replaces the state, tape contents, and head position by the specified values. Since there is only one register, its index is $0$; the other configuration fields—the input-head position and output—are unchanged. These are exactly the fields of the configuration with state $s'$ and counter $n$.
