<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.mem_Icc_of_abs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Bound Gives an Interval

**Claim.** For integers $p,q,R$, if $|p-q|\leq R$, then $p$ lies in the closed integer interval from $q-R$ to $q+R$.

**Proof.** The absolute-value bound is equivalent to $-(R)\leq p-q\leq R$. Rearranging the left inequality gives $q-R\leq p$, and rearranging the right gives $p\leq q+R$. These are precisely the two endpoint inequalities defining the closed interval.
