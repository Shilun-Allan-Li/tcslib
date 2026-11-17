<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.inWin_runWith_of_decides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runs Remain Within the Deciding Space Bound

**Claim.** If the machine decides the language within space bound $sp$, then every finite choice word, when run from the initial configuration on $x$, ends in a configuration whose work-tape heads and contents lie within the window of radius $sp(|x|)$.

**Proof.** Choose the time bound $T$ supplied by the deciding-space hypothesis for input $x$. If the choice word $w$ has length at most $T$, extend it to length $T$ by appending false choices. The extended run uses at most the prescribed space; the theorem that every prefix of a run using at most that space lies in the corresponding window (`Turing.NDTM.runWith_take_inWindow`) applies to the prefix of length $|w|$, which is exactly the original run. If $|w|>T$, consider its first $T$ choices. The configuration after those choices is halted by the time-bound hypothesis, so further choices leave it unchanged (`Turing.NDTM.runWith_of_halt`); the append law for runs (`Turing.NDTM.runWith_append`) identifies the full run with this halted configuration. Applying the same prefix-window theorem to the length-$T$ run proves the required window bound.

**Key facts.** `Turing.NDTM.runWith_take_inWindow`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`.
