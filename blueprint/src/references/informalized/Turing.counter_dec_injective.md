<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_dec_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Decrement Exit Map

**Claim.** The map from flag phases to counter-loop states, sending the successful completed phase to the body state at $a$, the unsuccessful completed phase to the finished state, and every other phase to its corresponding decrement state, is injective.

**Proof.** Suppose two phases have the same image. The three possible image forms are a body state, the finished state, and a decrement state. These forms are disjoint, so the phases must belong to the same case of the definition. In the body case both phases are the successful completed phase; in the finished case both are the unsuccessful completed phase; and in the decrement case equality of the decrement states gives equality of the phases. Thus the original phases are equal.
