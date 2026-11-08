<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopBody_stop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stopping at the Unreleased Anchor

**Claim.** When the body is in anchor state $a$ and the release bit is false, one wrapper step removes the state, leaves the release bit false, and sets the flag to false, regardless of its previous optional value.

**Proof.** At state $a$ with release bit false, the wrapper takes its stopping branch. That branch halts immediately, does not move the input head (the zero-movement fact `moveInputPos_zero`), leaves every body tape and head position unchanged, and writes false in the extra flag cell. The output is unchanged as well. These componentwise agreements give the stated embedded configuration with no state and flag false.

**Key facts.** `Turing.moveInputPos_zero`.
