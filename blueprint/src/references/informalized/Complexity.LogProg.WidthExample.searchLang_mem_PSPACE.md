<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidthExample.lean :: Complexity.LogProg.WidthExample.searchLang_mem_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Search Preserves Polynomial Space

**Claim.** If a Boolean-word language $P$ is decidable in polynomial space, then its search language, whose members are those $x$ for which some $u<2^{|x|}$ has the encoded pair of $x$ and the binary expansion of $u$ in $P$, is also decidable in polynomial space.

**Proof.** 1. Apply the polynomial-space construction for alternating register programs (`arm_decides_pspace_val`) to the search program. Its two oracle languages are the input-length language and $P$: the former is in polynomial space because log space is contained in polynomial space (`LOGSPACE_subset_PSPACE` and `inputLenLang_mem`), and the latter is in polynomial space by hypothesis. The construction will establish that the program halts with the desired answer while all registers stay within a bound of the form $2^{C(|x|+1)^c}$.

2. On input $x$, set $n=|x|$ and take the program's register bound to be $B=2^{n+1}$. This bounds both $2^n$ and $n$. Begin with all four registers zero; this initial configuration satisfies the program's register guard (`guard_rf`). The program first scans the input, querying the input-length language on encoded pairs with candidate lengths. Those queries answer whether the scanned count is still below $n$, so the scan terminates with the first register equal to $n$ (`indicator_indexLang_pairEncode`, `inputLength_loop`). The register updates preserve the intended first and second coordinates (`rf_1`, `rf_upd1`, `rf_upd0`).

3. Next the program doubles its second register exactly $n$ times. The doubling loop reaches the enumeration state with that register equal to $2^n$ (`dbl_loop`); its initial counter is zero, so the loop's starting case uses $2^0=1$.

4. Finally, the enumeration loop tests the candidates below $2^n$ against $P$ and halts with true exactly when at least one encoded pair belongs to $P` (`enum_loop`). This is precisely the membership condition defining the search language; the indicator and the definition of that language identify the loop's answer with the required decision. The polynomial-space construction therefore yields a polynomial-space decider for the search language.

**Key facts.** `Complexity.LOGSPACE_subset_PSPACE`, `Complexity.inputLenLang_mem`, `Complexity.LogProg.arm_decides_pspace_val`, `Complexity.LogProg.WidthExample.guard_rf`, `Complexity.LogProg.rf_1`, `Complexity.LogProg.rf_upd1`, `Complexity.LogProg.inputLength_loop`, `Complexity.LogProg.rf_upd0`, `Complexity.LogProg.WidthExample.dbl_loop`, `Complexity.LogProg.WidthExample.enum_loop`, `Complexity.indicator_indexLang_pairEncode`, `Complexity.LogProg.indicator_eq_decide`.
