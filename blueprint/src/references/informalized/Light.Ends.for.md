<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.for -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Execution of a For-Loop

**Claim.** If the loop invariant holds initially, is advanced by each body execution, and makes the upper-bound expression safely equal to $n$ through index $n$, then the for-loop terminates within the stated cost bound in a state satisfying $Q$.

**Proof.** After setting the loop index to zero, the initial hypothesis gives the invariant at index $0$. Apply the constant-bound loop theorem (`Light.Ends.whileConst`) to the while-loop that defines the for-loop, using the invariant that the local index is $j$ and $I(j)$ holds. At each $j<n$, the bound hypothesis makes the guard safe and true, since its value is $n$; the round hypothesis executes the body, preserves the index at $j$, and establishes the next invariant. The following increment is safe because $j+1\le n\le\mathrm{word}$, and it changes the index to $j+1$. At $j=n$, the same bound hypothesis makes the guard safe and false, and the terminal invariant gives $Q$. Finally, the initial assignment, the per-round guard/body/increment costs, and the final guard cost are bounded by the displayed expression for $T$; sequencing the initial assignment with the loop yields the claimed execution.

**Key facts.** `Light.Ends.seq`, `Light.Ends.set`, `Light.Ends.whileConst`.
