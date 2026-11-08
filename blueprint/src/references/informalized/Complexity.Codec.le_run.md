<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.le_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register comparison run

**Claim.** Starting at the comparison instruction, the program reaches the clearing instruction exactly when $v(r_{\mathrm{Pos}})\le v(r_{\mathrm{N1}})$, and otherwise reaches the rejecting instruction. The final register contents agree with $v$ except that $r_T$ contains the minimum of those two values, and every earlier configuration satisfies the run guard with bound $B$.

**Proof.** The comparison loop is an instance of the general register comparison lemma (`le_loop`). Its two tests compare the temporary register first with $r_{\mathrm{Pos}}$ and then with $r_{\mathrm{N1}}$: when the first equality holds, the loop ends; when the second equality holds first, it rejects; otherwise it increments the temporary register and repeats. Thus the loop terminates at the smaller of the two fixed register values, selecting the clearing instruction precisely when $v(r_{\mathrm{Pos}})\le v(r_{\mathrm{N1}})$, and leaving $r_T$ equal to their minimum. The hypotheses needed to apply the lemma hold: the two comparison registers are distinct from $r_T$, the specified instructions in the program are respectively these equality tests, the increment, and the two exits, and initially $r_T=0$ is at most either comparison value. Finally, all registers stay within $B$: the comparison registers do not change and the temporary register never exceeds their values. The loop lemma also supplies the run-guard condition for every configuration before the final one.

**Key facts.** `Complexity.Codec.le_loop`.
