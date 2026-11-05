<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: SwitchingLemma.numFree_update_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Fixing a Free Variable Lowers the Free Count by One

**Claim.** Let $\rho$ be a restriction on $n$ variables — a function assigning to each variable either a Boolean value or the symbol "free" ($\mathrm{none}$) — and let $v$ be a variable that is free under $\rho$. For any Boolean value $b$, form the restriction $\rho'$ by setting $v$ to $b$ and leaving every other variable as it was in $\rho$. Writing $f(\rho)$ for the number of free variables of $\rho$, we have $f(\rho') + 1 = f(\rho)$: fixing one free variable removes exactly one variable from the free set.

**Proof.** Recall that the free set $\mathrm{freeVars}(\rho)$ is the set of variables $i$ with $\rho(i) = \mathrm{none}$, and $f(\rho)$ is its cardinality. The entire argument is the observation that passing from $\rho$ to $\rho'$ deletes exactly the element $v$ from this set.

1. **$v$ lies in the free set of $\rho$.** By hypothesis $\rho(v) = \mathrm{none}$, which is precisely the membership condition for $\mathrm{freeVars}(\rho)$; hence $v \in \mathrm{freeVars}(\rho)$.

2. **The new free set is the old one with $v$ deleted:** $\mathrm{freeVars}(\rho') = \mathrm{freeVars}(\rho) \setminus \{v\}$. This is checked variable by variable. For $v$ itself, $\rho'(v) = b$ is a genuine Boolean, so $v$ is *not* free under $\rho'$ and belongs to neither side (the right-hand side excludes it by the deletion). For any other variable $i \neq v$, the update left $\rho$ untouched, so $\rho'(i) = \rho(i)$ and $i$ is free under $\rho'$ exactly when it is free under $\rho$; deleting $v$ does not affect the status of $i \neq v$. The two sides thus contain the same variables.

3. **Count the deletion.** Since $v$ is an element of the finite set $\mathrm{freeVars}(\rho)$, removing it lowers the cardinality by one, $\lvert \mathrm{freeVars}(\rho) \setminus \{v\} \rvert = \lvert \mathrm{freeVars}(\rho)\rvert - 1$ (`Finset.card_erase_of_mem`). Because $v$ witnesses that $\mathrm{freeVars}(\rho)$ is nonempty, its cardinality $f(\rho)$ is strictly positive, so the subtraction of one on the natural numbers loses nothing. Rearranging $f(\rho') = f(\rho) - 1$ gives $f(\rho') + 1 = f(\rho)$, as claimed.
