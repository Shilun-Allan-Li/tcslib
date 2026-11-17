<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean :: Turing.clearTM_contract_traj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unchanged Heads on Other Tapes

**Claim.** Throughout the clearing-machine contract, each tape other than the cleared tape has its head at its initial position.

**Proof.** Fix a valid run, a time within the contract's running time, and a tape $j\ne i$. The contract's head-envelope property places the head position on tape $j$ in the interval from its lower bound to its upper bound. Since $j\ne i$, both bounds equal the initial head position on that tape. The interval therefore contains only that position, forcing the head to remain there.
