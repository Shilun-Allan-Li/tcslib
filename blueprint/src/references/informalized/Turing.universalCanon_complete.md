<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCanon_complete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the canonizer

**Claim.** For Boolean words $\alpha$ and $x$, the buffered composition of the prefix parser and the canonizer halts after exactly $3|\alpha|+4+T_c(|\alpha|)$ steps, outputs the serialization of the machine decoded from $\alpha$, and has its input head at position $2|\alpha|+3$.

**Proof.** Apply the buffered-run description (\texttt{universalCanon\_run}) at $t=T_c(|\alpha|)$. It identifies the composite machine’s configuration at the stated time with a buffered second-phase configuration whose canonizer component is the canonizer’s run on $\alpha$ for that many steps, and whose physical input head is at position $2|\alpha|+3$. By the defining computation property of the canonizer and the equivalence between computing in time and halting with the specified output (\texttt{computesInTime\_iff}), that component is halted and has output $(c.decode\,\alpha).serialize$. The buffered configuration carries that same state and output, giving all three conclusions.

**Key facts.** `Turing.universalCanon_run`, `Turing.FinTM.computesInTime_iff`.
