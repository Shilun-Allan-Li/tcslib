<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Search.lean :: Complexity.LogProg.ExpBFS.count_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marked-Code Counting Run

**Claim.** Under the stated register, memory, and bound hypotheses, the machine’s count search reaches its designated branch with $U=K$ and with $c$ increased by the number of marked memory positions indexed from $U$ up to, but excluding, $K$, while preserving all other registers and satisfying the guard throughout the run.

**Proof.** Proceed by strong induction on $j=K-U$, keeping the full register state and memory as induction data. If $U=K$, the initial branch goes directly to the designated endpoint. The interval of indices is empty, so its filtered cardinality is zero; the endpoint state is unchanged, and the single transition is covered by the one-step reachability rule.

Otherwise $U<K$. The machine first clears its working register and change flag, then tests the memory bit at the address $Bs+U$. The memory-access run lemma (`ac_run`) carries out this access and returns to the counting loop, preserving the registers and head position; at this site the access reads rather than changes memory. The number of marked positions in $[U,K)$ is the contribution of the first index, plus the number in $[U+1,K)$ (`card_filter_Ico_succ`). If the bit at $Bs+U$ is true, the routine increments $c$ and $U$; if it is false, it increments only $U$. In either case the resulting state satisfies the induction hypotheses with gap $K-(U+1)=j-1$: the bounds follow from the original bounds and the assumed capacity for the count. The induction hypothesis handles the remaining interval. Concatenating the access run, the appropriate one- or two-transition update, and that recursive run gives the required guarded reachability. The one-step rule (`step_of`) and reachability concatenation (`MReach.trans`) justify these joins; reflexive reachability (`MReach.refl`) covers the terminal case.

**Key facts.** `Complexity.LogProg.ExpBFS.step_of`, `Complexity.LogProg.MReach.refl`, `Complexity.LogProg.ExpBFS.ac_run`, `Complexity.LogProg.ExpBFS.card_filter_Ico_succ`, `Complexity.LogProg.MReach.trans`, `Complexity.LogProg.ExpBFS.St.toV_U`.
