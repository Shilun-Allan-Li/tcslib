<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipActionK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Fixed-Count Action Skipper

**Claim.** For each fixed $k$, the partial reader that consumes the specified valid pairs, repeats the unrestricted two-bit consumption $k$ times between them, then reads the bounded state field, is jointly primitive recursive in the bound and input string.

**Proof.** The reader is a sequence of partial operations: consume the initial pair satisfying the validity condition, perform the work operation $k$ times, consume another valid pair, and read the state field with bound $n+1$. The two-bit skipper and bounded-state skipper are primitive recursive. The work operation is primitive recursive as well, and counted iteration gives primitive recursiveness of its $k$ repetitions (viewing the fixed count as a constant parameter). Each stage takes the suffix returned by the preceding stage through option bind, which preserves primitive recursiveness and propagates failure. Composing these stages proves the result.

**Key facts.** `Turing.codePrimRepeat`, `Turing.codePrimSkipPair`, `Turing.codePrimSkipState`, `Turing.codePrimSkipWork`.
