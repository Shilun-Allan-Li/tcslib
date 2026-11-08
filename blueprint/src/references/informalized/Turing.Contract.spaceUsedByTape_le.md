<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.spaceUsedByTape_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound from a Head Envelope

**Claim.** The number of distinct cells visited by a work-tape head through the contract time is at most the number of integer positions in the contract’s head-position interval, namely $(C.\mathrm{hi}(i,d,j)+1-C.\mathrm{lo}(i,d,j)).\mathrm{toNat}$, equivalently the positive part of that integer bound.

**Proof.** The contract envelope places the head position in the interval from $C.\mathrm{lo}(i,d,j)$ to $C.\mathrm{hi}(i,d,j)$ at every time up to and including the contract time. The visited-cell bound for an interval (`Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`) applies to these positions and bounds the number of distinct visited cells by $(C.\mathrm{hi}(i,d,j)+1-C.\mathrm{lo}(i,d,j)).\mathrm{toNat}$. For an integer, this natural-number conversion is its positive part, as in the stated maximum expression.

**Key facts.** `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`.
