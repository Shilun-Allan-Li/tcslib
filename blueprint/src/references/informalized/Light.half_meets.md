<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.half_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the halving program

**Claim.** Under the stated word bound and program-position hypothesis, the halving program, started with input $h$ and memory $\mu$, executes within the given time bound, returns $\lfloor(h+1)/2\rfloor$ at location $0$, and preserves memory.

**Proof.** First, the program is present at position $p$, so it suffices to establish the required execution for its body (the fact that a body execution yields the claimed program-position behavior is `Meets.of_body`). The body initializes the candidate register to zero, runs a loop that increments it while twice the candidate is less than $h$, and then copies the candidate into the argument register.

For the loop, use the invariant that after $i$ rounds the state has frame $[h,i]$ and memory $\mu$. It holds initially because the candidate was set to zero. Whenever $i<\lfloor(h+1)/2\rfloor$, the loop condition holds, and incrementing the candidate produces the frame $[h,i+1]$ while leaving memory unchanged. At $i=\lfloor(h+1)/2\rfloor$, the condition fails: twice this value is at least $h$. The loop execution rule packages these round-by-round facts and the exit condition into a bounded execution (`Ends.whileBlock`). The word bound ensures the loop's arithmetic expressions and test are safe.

Finally, copying the candidate to the argument register leaves location $0$ equal to $\lfloor(h+1)/2\rfloor$ and does not change memory. Composing initialization, loop, and final assignment gives the stated bound and result (`Ends.next`).

**Key facts.** `Light.Meets.of_body`, `Light.Ends.whileBlock`, `Light.update_frame_setLocal`, `Light.Ends.next`.
