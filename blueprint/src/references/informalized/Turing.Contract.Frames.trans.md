<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.Frames.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frames Under Contract Composition

**Claim.** If the first and second contracts preserve work-tape contents outside their respective frame sets, then the composed contract preserves contents outside the union of those frame sets, with the second evaluated at the linked parameter and first endpoint.

**Proof.** Fix a parameter and starting configuration satisfying the first contract's entry-state and precondition hypotheses. The first frame property gives equality of tape contents between the start and the first endpoint at every position outside the first frame. The first contract's endpoint lies in its singleton exit set, so its state is the second contract's entry state; the linked-precondition hypothesis therefore permits applying the second frame property at that endpoint. For any position outside the union, both equalities apply, and transitivity of equality shows that the initial and final contents agree. The fact used to combine these two preservation statements is the transitivity of preservation outside frames (Turing.Cfg.SameOutside.trans).

**Key facts.** `Turing.Cfg.SameOutside.trans`.
