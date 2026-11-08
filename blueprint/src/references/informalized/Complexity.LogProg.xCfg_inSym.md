<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.xCfg_inSym -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol After Configuration Update

**Claim.** For any configuration and update data, the updated configuration reads the input symbol at the specified input-head position, interpreting the two boundary positions as blank.

**Proof.** The input symbol of any configuration is determined by its input-head position: it is blank when the position is zero, and otherwise it is the input list's entry immediately before that position. The update sets the input-head position to $ip$ and does not change the input word. Applying the input-symbol characterization (\texttt{Complexity.LogProg.inputSymbol\_eq}) therefore gives exactly the value defined by $\mathrm{inSym}(x,ip.\mathrm{val})$, including the blank boundary case.

**Key facts.** `Complexity.LogProg.inputSymbol_eq`.
