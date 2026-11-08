<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.pal_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Palindrome Test Phase

**Claim.** If $i\le |x|$ and $|x|=i+r$, then from the test configuration with input head at position $i+1$, work head at $|x|-1-i$, and the first $|x|$ bits copied, after $r+1$ steps the machine is halted and outputs the one-bit word whose bit is true exactly when $x$ agrees with its reversal at every position from $i$ onward.

**Proof.** Induct on the number $r$ of remaining input positions. If $r=0$, the relation $|x|=i+r$ forces $i=|x|$. There are no positions $j$ with $|x|\le j<|x|$, so the agreement condition is vacuous. The machine is at the end marker in its test state; its transition halts and outputs the corresponding true bit. Now suppose $r+1$ positions remain. Then $i<|x|$, and the machine reads $x_i$ (`inputSymbolInner`) while its work-head symbol is the opposing bit $x^{\mathrm{rev}}_i$ (`pal_test_read`). If these bits agree, the test transition advances to the next comparison configuration (`pal_test_step`). The remaining run is covered by induction with starting index $i+1$ and $r$ positions left. The agreement condition from $i$ onward is equivalent to the condition from $i+1$ onward in this case, by `palMatches_succ`; hence the induction conclusion gives the required output and halt status. If the bits disagree, the condition from $i$ onward is false, witnessed already at position $i$. The machine's transition immediately halts with output `[false]`, and every later run remains at that halted configuration (`runFrom_of_halt`). This gives the asserted result in the mismatch case as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.inputSymbolInner`, `Complexity.pal_test_read`, `Complexity.pal_test_step`, `Complexity.palMatches_succ`, `Turing.MultiTapeTM.runFrom_of_halt`.
