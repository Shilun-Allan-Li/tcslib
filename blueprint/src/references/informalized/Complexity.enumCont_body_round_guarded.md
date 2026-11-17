<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_round_guarded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guarded body round

**Claim.** Under the two halting hypotheses, the body machine started at its anchor has a bounded positive time at which it accepts when the verification bit is true and otherwise returns to the anchor carrying the fixed-width increment (or the original word on overflow). No strictly intermediate positive-time configuration is at the anchor.

**Proof.** Apply the raw body-round result with the stop flag enabled. It gives a time $r$ within the stated bound minus one at which the computation from the verification phase either halts with output $[\mathrm{true}]$ or reaches the anchor. In the false-bit case, the raw endpoint is the anchor; the false-stop and true-stop machines agree at every other state, and the true-stop machine loops at the anchor. The first-anchor principle therefore shortens this run to its first visit to the anchor, at some time $t\le r$, without changing the endpoint. Start instead from the requested anchor configuration: its first step departs into verification mode, so take the final time to be $t+1$. The departure identity identifies the remaining run with the one just analyzed; it also transfers the strict intermediate-time avoidance to every positive time before $t+1$. In the true-bit case, the halt and output are preserved by agreement of the machines away from the anchor. In the false-bit case, the endpoint is exactly the anchor configuration with the incremented word, using the original word when the increment overflows. The added departure step gives the claimed bound and positivity.

**Key facts.** `Complexity.enumCont_body_round_raw`, `Complexity.enumCont_body_agree`, `Complexity.enumCont_first_anchor`, `Complexity.enumCont_halt_transfer`, `Complexity.enumCont_body_depart`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
