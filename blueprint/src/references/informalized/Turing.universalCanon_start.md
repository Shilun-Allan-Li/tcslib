<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCanon_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonizer after prefix extraction

**Claim.** After $3|\alpha|+4$ steps on the paired input, the buffered composition is in the second-phase configuration with the canonizer at its initial configuration on $\alpha$, virtual-boundary flag true, and physical input head at position $2|\alpha|+3$.

**Proof.** Split $3|\alpha|+4$ into $2|\alpha|+2$ steps followed by $|\alpha|+2$ steps, and use the run concatenation law (\texttt{runFrom\_add}). The paired encoding consists of the doubled bits of $x$, a two-bit delimiter, and then $\alpha$; the paired-input length identity (\texttt{universal\_pair\_length}) supplies the corresponding position arithmetic. During the first segment the prefix parser remains live at every earlier time (\texttt{universalPrefix\_live}), so the buffered first-machine simulation lemma (\texttt{bufferedFirstCfg\_run}) applies. At the end of this segment, the parser’s configuration is the one given by its start-position description (\texttt{universalPrefix\_start}). The buffered first-phase initialization identity (\texttt{bufferedFirstCfg\_init}) identifies the composite machine’s initial configuration with this first-phase setup. Finally, the parser is halted there; the buffered rewind lemma (\texttt{bufferedFirstCfg\_rewind}) says that the next $|\alpha|+2$ steps transfer its output to the canonizer’s input and start the canonizer, with the flag true and the specified physical head position. Together these identifications give the claimed configuration.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.bufferedFirstCfg_init`, `Turing.FinTM.bufferedFirstCfg_run`, `Turing.universalPrefix_live`, `Turing.universalPrefix_start`, `Turing.FinTM.bufferedFirstCfg_rewind`, `Turing.universal_pair_length`.
