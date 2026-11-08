<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.laneCfg_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Focusing the setup lane

**Claim.** Focusing the first additional work tape of the setup configuration replaces its head position and tape by frontier $z$ and the sweep tape determined by $z,l,r$, while updating the setup phase and preserving the other setup data.

**Proof.** Compare configuration fields. The state changes to $q'$, the input position stays $p$, and the output is preserved. Split the work tapes and their head positions into the original $W.k$ tapes and the three added tapes. The original tapes are unaffected because their indices differ from the focused lane. Among the three added tapes, the focused lane is the first; the other two retain head positions $u,g$ and tapes $ut,gt$. The three added indices are exhausted by the cases $0,1,2$ (\(\texttt{Complexity.finThree_cases}\)). At index $0$, the updated head position is $z$ and the updated tape is the required sweep tape, giving the claimed setup configuration.

**Key facts.** `Complexity.finThree_cases`.
