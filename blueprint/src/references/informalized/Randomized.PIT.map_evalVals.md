<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.map_evalVals -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation modulo a positive integer

**Claim.** For positive $k$, mapping the natural-number evaluation list into $\mathbb Z/k\mathbb Z$ agrees with evaluating the gates in that ring, and every natural-number entry produced is less than $k$.

**Proof.** Induct on the gate list, proving both assertions for every initial list whose entries are less than $k$. With no gates, evaluation leaves the initial list unchanged, so both conclusions hold. For a first gate $g$, its natural-number value is less than $k$ by the gate-value range fact (`Randomized.PIT.gateVal_lt`). The old entries already satisfy the bound, so every entry of the list extended by this value still does. Apply the induction hypothesis to the remaining gates with this extended initial list. For the correspondence, map the initial list and the appended singleton into the ring; the value of the new singleton agrees with the ring evaluation of $g$ by the natural-cast gate-value identity (`Randomized.PIT.natCast_gateVal`). The induction hypothesis identifies the mapped evaluation of the remaining gates, completing the list equality as well as the range assertion.

**Key facts.** `Randomized.PIT.gateVal_lt`, `Randomized.PIT.natCast_gateVal`.
