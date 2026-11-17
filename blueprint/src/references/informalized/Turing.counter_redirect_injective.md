<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counter_redirect_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Redirect

**Claim.** The counter-loop redirect is injective: distinct states cannot be sent to the same counter-loop state.

**Proof.** Suppose two states $s,t$ have the same image. Split according to whether each equals the distinguished state $a$. If both equal $a$, they are equal. If exactly one equals $a$, its image is the decrement state; the other state can only map to an escape state or a body state, so the images cannot agree. If neither equals $a$, split according to whether the optional exit is that state. An exit state maps to the escape constructor, while any non-exit state maps to the body constructor; these constructors are disjoint. If both map to body states, equality of the body payloads gives $s=t$. Thus in every case the original states are equal.
