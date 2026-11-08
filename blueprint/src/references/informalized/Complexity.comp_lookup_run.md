<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_lookup_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Lookup Computation

**Claim.** From the specified seek state and register values, the computation halts with the length test for $\langle f(x),b\rangle$ in length mode, and with its indexed bit otherwise, while maintaining the required conditions.

**Proof.** Let $n=2|f(x)|$, the length of the doubled first component in the output pair. The total-length hypothesis implies $n\le B$. The seek computation (\texttt{comp\_seek\_run}) searches the first $n$ positions, respecting the register bound. If $p<n$, it reaches the prefix-hit state with the address registers set to $p$. The prefix-hit result (\texttt{comp\_prefix\_hit}) is true in length mode; in bit mode it reads the corresponding bit of $f(x)$. The pair-encoding bit formula (\texttt{pairEncode\_getD}) identifies this with the bit at position $p$ of $\langle f(x),b\rangle$, and $p<n$ ensures this position is in the doubled first component. If $p\ge n$, the search reaches the separator state. The separator computation (\texttt{comp\_separator\_run}) handles the separator and suffix and returns exactly the required length or bit answer. Each branch's halting result is combined with the preceding reachable computation by (\texttt{AReach.halt}); updated counters remain bounded by (\texttt{register\_update\_le}).

**Key facts.** `Turing.length_pairEncode`, `Complexity.comp_seek_run`, `Complexity.LogProg.register_update_le`, `Complexity.comp_prefix_hit`, `Complexity.pairEncode_getD`, `Complexity.comp_separator_run`, `Complexity.LogProg.AReach.halt`.
