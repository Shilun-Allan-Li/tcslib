<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_valid_inner -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity Check from Inner Preparation

**Claim.** Under the polynomial output-length bound, canonicality of $b$, and the stated register hypotheses, the machine starting in its inner-preparation state halts with the specified length answer or output bit, and maintains step-validity and the register bound throughout.

**Proof.** Let $h$ be the encoded input and let $B$ be its stated register bound. The encoding-length formula (Turing.length_pairEncode) gives $|x|\le |h|$. The output-size estimate for the composed encoding (compQ_host_cap), together with the identification of that output on canonical suffixes (compQ_field), bounds $|\langle f(x),b\rangle|$ by $B$. In particular, $2|f(x)|\le B$. The power bound (comp_power_bound) also ensures that the polynomial workspace value fits within $B$. Updating registers to their preparation values therefore preserves the bound (register_update_le).

The inner-preparation routine reaches the length-search state with register $8$ set to $|x|+1$ and register $7$ set to $C(|x|+1)^e$ (comp_inner_prepare). The assumed output-length estimate supplies the required cap on register $7$. For every queried index below that cap, the lifted oracle agrees with the length or bit predicate for $f(x)$ (comp_lifted). Thus the length-search routine correctly leaves the output length in register $12$ (comp_length_search). A register-scaling loop then transfers twice that length into register $11$ and clears register $12$; its invariant fits because $2|f(x)|\le B$ (registerScale_loop).

At this point the lookup routine's register hypotheses hold: the input head is reset, the source and output lengths are represented in the required registers, and the original position remains in register $5$. The output encoding fits within $B$, as shown above, so the lookup routine halts with the requested length comparison in mode and with the requested bit otherwise (comp_lookup_run). The reachability segments compose by transitivity (AReach.trans); halting after a reached configuration is preserved (AReach.halt), and the initial configuration satisfies the step-validity condition (comp_preS). These facts give the claimed run from the inner-preparation state with the bound and validity condition maintained throughout.

**Key facts.** `Turing.length_pairEncode`, `Complexity.compQ_host_cap`, `Complexity.compQ_field`, `Complexity.comp_power_bound`, `Complexity.LogProg.register_update_le`, `Complexity.comp_inner_prepare`, `Complexity.comp_lifted`, `Complexity.comp_length_search`, `Complexity.LogProg.registerScale_loop`, `Complexity.comp_lookup_run`, `Complexity.LogProg.AReach.trans`, `Complexity.LogProg.AReach.halt`, `Complexity.comp_preS`.
