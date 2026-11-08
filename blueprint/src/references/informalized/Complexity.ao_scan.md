<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.ao_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan Test for a Suffix of Ones

**Claim.** When $|x|=p+r$, running the machine for $2r+3$ steps from the specified encoded input and configuration halts with output true exactly when $b$ is true and every bit of $x$ from index $p$ onward is true.

**Proof.** Proceed by induction on $r$, using the pair encoding’s layout: each bit $x[j]$ occurs twice, the separator is $[\mathrm{false},\mathrm{true}]$, and the advice bit follows it (\texttt{Complexity.pairEncode_getElem?}); the encoded length is $2|x|+2+1$ (\texttt{Turing.length_pairEncode}). At each needed position, the auxiliary lookup fact turns a known list lookup into an actual indexed bit and its validity bound (\texttt{Complexity.getElem_of_getElem?_eq}).

For $r=0$, the length condition forces $p=|x|$, so the suffix condition is vacuous. The machine takes two moves through the separator, then halts on the advice bit and outputs $b$. The halting-step lemma supplies that final state and output (\texttt{Complexity.ao_halt}); once a configuration is halted, any remaining run steps leave it unchanged (\texttt{Turing.MultiTapeTM.runFrom_of_halt}). Thus its output is true exactly when $b$ is true.

For the successor case, $p<|x|$. If $x[p]=\mathrm{true}$, the machine takes two moves across the duplicated copies of this bit and returns to state $0$ at the next scan position. The remaining run is the induction hypothesis with starting index $p+1$. The condition that all bits from $p$ onward are true is equivalent, in this case, to the same condition from $p+1$ onward, since the bit at $p$ is true. If instead $x[p]=\mathrm{false}$, the machine moves to the rejecting scan state and halts on the second copy of that bit, outputting false. The suffix condition is then false because its first required bit is false. In both branches the prescribed state transitions and head advances are given by the move lemma (\texttt{Complexity.ao_move}), and the immediate halting behavior by the halting-step lemma (\texttt{Complexity.ao_halt}). The run-length decompositions used in these steps follow from splitting a run into its first step and the remaining run (\texttt{Turing.MultiTapeTM.runFrom_succ_eq_step}).

**Key facts.** `Complexity.pairEncode_getElem?`, `Turing.length_pairEncode`, `Complexity.getElem_of_getElem?_eq`, `Complexity.ao_halt`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.ao_move`.
