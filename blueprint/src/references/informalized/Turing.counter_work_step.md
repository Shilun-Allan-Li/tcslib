<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_work_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Symbol Relabelling Preserves a Step

**Claim.** Relabelling a machine's work-tape symbols by a bijection and then taking one step gives the same configuration as taking a step first and then relabelling the work-tape symbols.

**Proof.** If the configuration is halting, both steps leave it unchanged apart from the stipulated relabelling of its work tapes, so the two results agree. Otherwise let $s$ be its state. The relabelled configuration presents each work-head symbol after applying the bijection; the relabelled machine decodes this symbol with the inverse bijection before consulting the original transition. Because the bijection followed by its inverse is the identity, the original transition sees exactly the original work symbols. Its input movement, output, and successor state are unchanged, while each written work symbol is relabelled by the bijection. The head movements are unchanged as well. At each tape position, either the transition writes nowhere, or it updates precisely the current head position with that relabelled symbol; all other positions retain the already relabelled tape contents. Thus every configuration component agrees with taking the original step and then relabelling.
