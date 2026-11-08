<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.gs_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-Set Characterization of the Recursive Condition

**Claim.** The recursive condition making $r$ successive choices between $A$ and $B$, starting at $(t,c)$ and ending with $\mathrm{Kont}$, holds exactly when there is a finite set $T$ in the interval from $t$ through $t+r-1$ on which $A$ holds, while $B$ holds at every other point of that interval, and $\mathrm{Kont}(c+|T|)$ holds.

**Proof.** Induct on $r$, with the starting position $t$ and counter $c$ arbitrary. If $r=0$, the interval is empty and the only possible set is empty; the assertion reduces to the terminal condition $\mathrm{Kont}(c)$. For the successor step, the first position is $t$ and the remaining interval begins at $t+1$.

1. Suppose the first choice uses $A$. By induction, the remaining choices are described by a set $T$ in the interval from $t+1$ through $t+r$, with $A$ on $T$, $B$ on the other positions there, and terminal condition $\mathrm{Kont}(c+1+|T|)$. The set $T$ cannot contain $t$, so adjoining $t$ gives a set for the full interval. Its cardinality is $|T|+1$, and the terminal counter is therefore $c+|T\cup\{t\}|$; $A$ holds at the newly adjoined point, while the conditions on later points are inherited.

2. Suppose the first choice uses $B$. The induction hypothesis supplies a set $T$ describing the remaining interval. Keep this set unchanged in the full interval. It omits $t$, where $B$ holds by the first choice; on the later positions the required $A$ and $B$ conditions come from induction. The terminal counter is unchanged, as is the set's cardinality.

3. Conversely, take a set describing the full interval. If it contains $t$, remove $t$ to obtain the set for the remaining interval and take the first choice to be $A$. The terminal counter agrees because removing one element decreases the cardinality by one, matching the increment already made to the counter. If the set omits $t$, take the first choice to be $B$ and use the same set for the remaining interval. The conditions on later positions and the terminal counter then follow directly. These two cases give precisely the two alternatives in the recursive definition.
