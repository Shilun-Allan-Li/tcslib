<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of a Clean Call

**Claim.** If $M$ halts on input $\mathrm{arg}$ with output $\mathrm{cap}$ after $T$ steps, the call machine reaches its designated exit configuration within $(24+13k)(T+|\mathrm{arg}|+|\mathrm{cap}|+1)$ steps, with the specified work tape and output determined by the mode $\mathrm{emit}$.

**Proof.** Let $a$ be the preparation time and $b$ the time used to process the $k$ banks. The preparation result (\texttt{emCall\_prepare\_run}) supplies a configuration ready to process bank zero with $a\le 2T+|\mathrm{arg}|+4$. The bank-processing result (\texttt{emCall\_banks\_run}), applied to all $k$ banks, gives the next configuration in time $b\le k(6T+8)$. Put $B=T+|\mathrm{arg}|+|\mathrm{cap}|+1$. Since $B$ dominates each of the input quantities, these bounds imply $b\le 13kB$ and $a+|\mathrm{arg}|+3|\mathrm{cap}|+6\le24B$. The finalization result (\texttt{emCall\_finalize\_run}) takes exactly $|\mathrm{arg}|+3|\mathrm{cap}|+6$ additional steps from the bank-complete configuration and produces the claimed exit configuration. The run-composition law (\texttt{Turing.MultiTapeTM.runFrom\_add}) combines these three stages, and their total time is at most $24B+13kB=(24+13k)B$.

**Key facts.** `Turing.FinTM.emCall_prepare_run`, `Turing.FinTM.emCall_banks_run`, `Turing.FinTM.emCall_finalize_run`, `Turing.MultiTapeTM.runFrom_add`.
