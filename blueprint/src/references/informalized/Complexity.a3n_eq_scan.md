<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_eq_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparator Scan Invariant

**Claim.** Starting from the stated comparison configuration, after any $j\le |v|$ steps the machine is still in comparison state, has advanced its input head by $j$, and has work word $u$ and work head at $j$; its flag records whether the length-$j$ prefixes of $u$ and $v$ agree.

**Proof.** We argue by induction on $j$. At $j=0$, the run has made no steps, both prefixes are empty and therefore agree, and the claimed configuration is the initial one. For the successor step, suppose the claim holds at $j$ and $j+1\le |v|$. The input head is at the position corresponding to the $j$th symbol of $v$, so the input symbol is $v[j]$ (by the input-symbol-at-an-interior-position fact, `Turing.inputSymbolInner`). The work head is at $j$, where the tape contains $u[j]$ when that position is within $u$; if it is beyond $u$, it reads blank. Thus the transition in comparison state advances the input head and work head by one, leaves the tape unchanged, stays in comparison state, and updates the flag by conjoining its old value with the test that the work symbol equals $v[j]$. The prefix-extension criterion (`Complexity.e3c_take_succ_eq`) says precisely that the old prefixes agree and the next symbols agree if and only if the length-$(j+1)$ prefixes agree; the option-valued lookup also handles the case where $u$ has ended. Hence the new flag has the required value. The run recurrence `Turing.MultiTapeTM.runFrom_succ_eq_step'` identifies this one transition with the run at $j+1$. Finally, the input head's rightward move advances its position by one, by `Turing.moveInputPos_pos_of_ne_right`, while the work-head position advances by the transition's unit move and the unchanged tape still represents $u$. This gives the claimed configuration at $j+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.inputSymbolInner`, `Complexity.e3c_take_succ_eq`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_pos_of_ne_right`.
