<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Dispatcher.lean :: Light.Compiler.codeAt_dispatcher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Individual dispatcher entries

**Claim.** If the dispatcher for $n$ procedures is a prefix beginning at $disp$, then for every $j<n$, the decrement-and-branch pair for procedure $j$ is a prefix beginning at $disp+2j$.

**Proof.** Because $j<n$, the dispatcher for $j$ procedures is a prefix of the dispatcher for $n$ procedures (\texttt{dispatcher\_prefix}). The dispatcher for $j+1$ procedures consists of that shorter dispatcher followed by the pair that decrements the remaining-procedure counter and branches to $j$ (\texttt{dispatcher\_succ}). Hence this concatenation is a prefix of the full dispatcher, and therefore of the code beginning at $disp$. Taking its final block places the pair immediately after the dispatcher for $j$ procedures. That dispatcher has length $2j$ (\texttt{length\_dispatcher}), so the pair begins at $disp+2j$.

**Key facts.** `Light.Compiler.dispatcher_prefix`, `Light.Compiler.dispatcher_succ`, `WordRAM.CodeAt.right`, `Light.Compiler.length_dispatcher`, `WordRAM.CodeAt.cast_pos`.
