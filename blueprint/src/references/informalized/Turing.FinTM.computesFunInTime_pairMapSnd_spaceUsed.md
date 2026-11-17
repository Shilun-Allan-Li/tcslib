<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair mapping with bounded space

**Claim.** Given a machine computing $g$ within time $T_g$ and using at most $S_g$ space, one can compute the pairing of the first parsed component with the image under $g$ of the second, returning the empty word on parse failure, in linear overhead over $T_g$, with space bounded by $S_g(|x|)+c(|x|+1)$.

**Proof.** Choose the mapped machine that either rejects an invalid pair or, after parsing a valid pair $(a,b)$, launches a virtual copy of $M_g$ on $b$. Set the common constant to $22$.

For the time bound, split according to whether parsing succeeds. On failure, the machine halts with empty output within $5(|x|+1)$ steps, by the rejection property of the mapped machine; this is below the claimed bound. On success, parsing supplies $x=\operatorname{pairEncode}(a,b)$, so both component lengths are at most $|x|$. The launch takes at most $5(|x|+1)$ steps, after which the virtual run simulates $M_g$ for $T_g(|b|)$ steps. The virtual-run correspondence transfers the halting state and the output of $M_g$; the saved prefix $\operatorname{pairEncode}(a,[])$ followed by $g(b)$ is exactly $\operatorname{pairEncode}(a,g(b))$. Monotonicity of $T_g$ and the component-length bound place this total time below $22(|x|+1+T_g(|x|))$.

For space, put $D=5(|x|+1)$. Every work head moves by at most one position per step, so during the launch each added head stays within distance $D$ of its initial position. After launch, the two bookkeeping heads remain within that same bound: the buffer head tracks the simulated input position, which is bounded by the input length, and the other head stays within the corresponding fixed region. The original work-tape heads either remain at their launch positions or track positions visited by the simulated machine. Consequently, their visited-position sets through any time $t$ are contained in those of the corresponding tapes of $M_g$ on $b$ through time $t$. Since $|b|\le |x|$, monotonicity of $S_g$ bounds the simulated contribution by $S_g(|x|)$. The mapping-space estimate combines this with the two bookkeeping tapes' $O(D)$ positions, yielding the stated bound after absorbing constants into $22$.

**Key facts.** `Turing.FinTM.a2_map_reject`, `Turing.FinTM.a2_map_launch`, `Turing.eq_pairEncode_of_pairDecode`, `Turing.length_pairEncode`, `Turing.FinTM.a2_mapVirtual_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_head_steps`, `Turing.FinTM.a2_mapSetup_heads`, `Turing.FinTM.tapeBlocks_left`, `Turing.FinTM.tapeBlocks_buffer`, `Turing.FinTM.tapeBlocks_right`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.FinTM.a2_map_space`.
