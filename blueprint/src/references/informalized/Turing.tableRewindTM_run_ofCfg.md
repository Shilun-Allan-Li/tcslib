<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.tableRewindTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding a Table Tape

**Claim.** Under the stated tape-content and initial-state hypotheses, the table-rewind machine reaches the right component's done phase after $L+7$ steps, with tape $i$'s head at its initial position minus $L$. It does not reach that done phase earlier; through time $L+7$, that head stays between its final and initial positions with the stated two-cell margin, and all other work-tape heads stay fixed.

**Proof.** Write $a=|ws|-1$, let $u\,=\,ws[a]$ be the final field, and let $pre$ be the preceding fields. The list is nonempty, so this final field exists; every field, including $u$, is nonempty. Split $ws=pre++[u]$. The offset decomposes as $L=\mathrm{fieldOffset}(pre,|pre|)+|u|+1$, by the successor formula for field offsets (`Turing.fieldOffset_succ`).

First regard the initial configuration as one for the skip-back machine, by replacing its left-component state with the corresponding run state. The global tape-content hypothesis, together with the fact that the final field occupies the final segment of the table (`Turing.fieldsTape_field`), supplies exactly the buffer-layout hypothesis needed to run skip-back across $u$. Its run theorem (`Turing.skipBackTM_run_ofCfg`) shows that this first phase takes $|u|+3$ steps, reaches its done state, and places tape $i$'s head just before the final field; it also gives the intermediate head bounds and rules out an earlier done state.

Now view the resulting configuration as the start of the seek-start phase, with its state reset to run. Since $u$ is nonempty, the tape symbol at the new head is present. The tape contents from there agree with the joined fields of $pre$: the slice identity for joined fields (`Turing.rt_fields_slice`) gives this agreement at nonnegative positions, while negative positions contain blanks by the definition of the tape representation. Thus the seek-start run theorem (`Turing.seekStartTM_run_ofCfg`) applies to $pre$. It takes $\mathrm{fieldOffset}(pre,|pre|)+4$ further steps, reaches done with the head at the beginning of the table, and supplies its own no-earlier-done and head-bound statements.

The two phases are joined by the seam-composition run theorem (`Turing.seamCompTM_run_ofCfg`), which includes the single transition from the left phase to the right. The time decomposition is $|u|+3+1+(\mathrm{fieldOffset}(pre,|pre|)+4)=L+7$. Hence the composed machine reaches the specified right-component configuration at precisely that time. The first-return theorem for seam composition (`Turing.seamCompTM_firstReturn_ofCfg`), applied to the no-earlier-done conclusions from the two phases, rules out reaching the right done state before then.

Finally, the seam-composition visited-head bound (`Turing.seamCompTM_visitedByTapeHead_ofCfg`) places every head position visited during the combined execution among those visited in one of the two phases. The bounds from the two phase theorems place tape $i$ within the claimed overall interval; for every other tape both phase bounds keep its head at its initial position. This gives the asserted bounds at every time through $L+7$.

**Key facts.** `Turing.fieldOffset_succ`, `Turing.fieldsTape_field`, `Turing.rt_fields_slice`, `Turing.skipBackTM_run_ofCfg`, `Turing.seekStartTM_run_ofCfg`, `Turing.seamCompTM_run_ofCfg`, `Turing.seamCompTM_firstReturn_ofCfg`, `Turing.seamCompTM_visitedByTapeHead_ofCfg`.
