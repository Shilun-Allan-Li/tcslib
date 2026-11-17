<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Fragment_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Tableau Fragment Selection

**Claim.** For the packed body word, the native fragment selector at position $j$ returns the serialized fragment of the group at position $j$ in the ordered tableau list with horizon $T=c\bigl(A(|x|+C(|x|+1)^e+1)^d+1\bigr)^2$, using the empty formula when the index is out of range.

**Proof.** Set $z$ to be the packed word, $m=|x|+C(|x|+1)^e$, and $T$ to the stated horizon. The packing identities show that the cursor read from $z$ is $j$ (`Turing.pairDecode_pairEncode`), the stored instance is $x$ and the stored round count is the prescribed last round (`Complexity.clA5Stored_exact`), and the input size and horizon recovered from the header are $m$ and $T$ (`Complexity.clA5Data_exact`). The selector’s ordered-list interpretation (`Complexity.clA5GroupAt_exact`) reduces the claim to checking which consecutive interval contains $j$. First, if $j<|x|$, the selected group is the pinning group for input bit $j$, exactly the selector’s first branch. Otherwise subtract the pinning block length: offset zero selects the initial group; the next $T$ positions select state-transition groups; the next $T+1$ select input groups; the next $k(T+1)$ select work groups, with quotient giving the time and remainder the tape; the final $T$ positions select acceptance groups. These are precisely the selector’s successive index tests. For input positions, the packed input selector agrees with the corresponding input group by `Complexity.clA5InputFragment_exact`; for work positions, the packed visit record yields the corresponding tape and time, and `Complexity.clA5WorkFragment_exact` identifies its serialized group. When the index lies beyond all listed groups, both sides return the empty formula, including the degenerate case of no work tapes.

**Key facts.** `Complexity.clA5Data_exact`, `Complexity.clA5GroupAt_exact`, `Complexity.clA5InputFragment_exact`, `Complexity.clA5Stored_exact`, `Complexity.clA5WorkFragment_exact`, `Turing.pairDecode_pairEncode`.
