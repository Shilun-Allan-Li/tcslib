<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_initializes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of the Schedule Configuration

**Claim.** Under the stated size bound and with a budget word $w$ of value $v$, there is a same-length word $w'$ such that the reset-start setup reaches the specified macrostep-check setup in the stated number of steps.

**Proof.** First choose $w'$ using the budget-processing result `setupCfg_budget_all`, with initial unary counter zero and the partial guide for the input length. This gives a word of the same length as $w$ and evolves the configuration from budget-start to unary-start, allocating $(a+1)(v+1)$ unary markers; the hypothesis $	ext{budgetValue}(w)=v$ supplies its required value condition. The reset scan then reaches the left end of the input in $p-1+2$ steps by `setupCfg_reset`. Copying the input guide takes $2|x|+4$ steps by `setupCfg_copy`, producing the partial guide for $|x|+1$ cells. These phases leave precisely the budget-start configuration required by the budget-processing result. Finally, apply `setupCfg_allocation` with $n=|x|$ and $B=(a+1)(v+1)$. The assumed bound ensures $n+1
	ext{le} B$, so this phase converts the partial guide into the radius-$3B$ guide and returns the unary head to $1$ in $14B+10$ steps. Concatenating the four run segments with `runFrom_add` gives the displayed total time and the desired final setup.

**Key facts.** `Complexity.setupCfg_budget_all`, `Complexity.setupCfg_reset`, `Complexity.setupCfg_copy`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.setupCfg_allocation`.
