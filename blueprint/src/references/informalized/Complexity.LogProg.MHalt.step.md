<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARM.lean :: Complexity.LogProg.MHalt.step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prepending one step to a halting run

**Claim.** If $G$ holds at configuration $a$ and the configuration after one step from $a$ halts with result $r$, with $G$ holding at every configuration strictly before that halt, then the machine halts with result $r$ from $a$ while $G$ holds at every configuration strictly before halting.

**Proof.** The single-step reach fact (\texttt{Complexity.LogProg.MReach.single}) says that the machine reaches its one-step successor from $a$, and that $G$ holds at the sole configuration strictly before that successor, namely $a$. The concatenation principle for a reach followed by a halting run (\texttt{Complexity.LogProg.MReach.halt}) then combines this initial one-step reach with the given halting run from the successor. It yields a halting run from $a$ with the same answer and with $G$ holding throughout all configurations strictly before the final halt.

**Key facts.** `Complexity.LogProg.MReach.single`, `Complexity.LogProg.MReach.halt`.
