<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.exists_of_iterate_absStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing an Iterated Absolute Step

**Claim.** If iterating the absolute parsing step $T$ times from $(w,vs)$ yields $([0],vs')$, then $w$ encodes a list of gates whose references are earlier than their positions after the initial values, and whose evaluation from $vs$ gives $vs'$.

**Proof.** We induct on the number $T$ of steps. At $T=0$, the hypothesis forces $w=[0]$ and $vs'=vs$, so the empty gate list has the required encoding, reference condition, and evaluation. For the successor step, inspect the first bit of $w$. If $w$ is empty, starts with $0$ followed by another bit, or starts with $1$ but its remainder does not parse as a gate, the step produces the empty word; subsequent steps leave it empty, so it cannot end at $[0]$. If $w=[0]$, the step fixes both components, and the empty gate list again works. The remaining case is $w=1::l$, where parsing yields a gate $g$ and remainder $l'$. If $g$ does not refer below the current value-list length, the step produces the empty word and cannot reach $[0]$. Thus it does refer below that length, and the first step changes the state to $(l',vs++[\mathrm{gateVal}(g)])$. Apply the induction hypothesis to the remaining iterations to obtain a list $gs$ encoded by $l'$, with its references below the length of the updated value list and with the required final evaluation. Prepending $g$ gives the encoding of the original word: the parsing equation says $l=g.encode++l'$ (`parse_eq_some`). The new first gate satisfies the reference condition by the case assumption; each later gate's bound becomes the original value-list length plus one plus its position, exactly the induction bound. Finally, the induction hypothesis's evaluation from the value list extended by $g$ is the successive evaluation of $g::gs$ from $vs$.

**Key facts.** `Randomized.PIT.parse_eq_some`.
