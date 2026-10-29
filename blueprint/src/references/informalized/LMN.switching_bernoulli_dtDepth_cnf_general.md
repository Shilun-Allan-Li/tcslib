<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: LMN.switching_bernoulli_dtDepth_cnf_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The Switching Lemma for Arbitrary CNF Formulas

**Claim.** Let $f$ be a CNF formula on $n>0$ variables of width at most $w$ (its widest clause has at most $w$ literals), with $w>0$. Fix a parameter $p$ with $0<p\le 1$ and $p\le \tfrac1{40w}$, and draw a $p$-Bernoulli random restriction $\rho$: each variable is left free independently with probability $p$, and otherwise fixed to $0$ or to $1$, each with probability $(1-p)/2$. Then for every threshold $t\in\mathbb N$, the probability that the restricted function $f|_\rho$ still requires a decision tree of depth more than $t$ is bounded by
\[
\Pr_{\rho}\big[\operatorname{dtDepth}(f|_\rho) > t\big] \;\le\; \left(\tfrac12\right)^{t} + \exp\!\left(-\tfrac{np}{3}\right).
\]
This is Håstad's switching lemma in its Bernoulli form: the first term is the genuine switching bound $(O(pw))^t$, while the additive $\exp(-np/3)$ absorbs the unlikely event that too few variables survive the restriction.

**Proof.** The real content of the switching lemma — the delicate counting-by-canonical-encodings argument — is carried by a companion theorem that assumes the CNF is **clean**: within every clause each variable occurs at most once, and so with a single determined sign (`SwitchingBernoulli.switching_bernoulli_dtDepth_cnf`). The theorem here makes no such assumption, so the entire task is to reduce the arbitrary case to the clean case. The reduction is a single preprocessing step, and the proof does nothing probabilistic itself.

1. **Cleaning the formula.** Let $\tilde f := \operatorname{cleanCNF}(f)$ be the cleaned form of $f$. Concretely, cleaning deletes repeated literals inside each clause and discards any clause that contains some variable both positively and negatively; such a clause is a tautological disjunction, always satisfied, and dropping it changes nothing. These are exactly the moves that make each clause var-injective and duplicate-free without touching the Boolean function or widening any clause.

2. **The cleaned formula computes the same function.** On every input $x\in\{0,1\}^n$ one has $\tilde f(x)=f(x)$ (`LMN.cleanCNF_eval`). Hence $\tilde f$ and $f$ are literally equal as Boolean functions: the proof replaces $\operatorname{eval}(f)$ by $\operatorname{eval}(\tilde f)$ throughout the goal by functional extensionality. Because the two functions are equal, for every restriction $\rho$ the restricted functions $f|_\rho$ and $\tilde f|_\rho$ coincide pointwise, so they have identical minimal decision-tree depth, and the two events $\{\operatorname{dtDepth}(f|_\rho)>t\}$ and $\{\operatorname{dtDepth}(\tilde f|_\rho)>t\}$ are the same event. The probabilities therefore agree, and it suffices to prove the bound for $\tilde f$.

3. **Discharging the cleanliness hypotheses.** The cleaned formula $\tilde f$ meets every precondition of the clean-case theorem:
   - its width is no larger than that of $f$, hence still at most $w$ (`LMN.cleanCNF_width_le`, composed with the hypothesis $\operatorname{width}(f)\le w$);
   - inside each clause the variable determines the literal, i.e. two literals of one clause sharing a variable are equal (`LMN.cleanCNF_var_inj`);
   - no clause repeats a literal (`LMN.cleanCNF_nodup`).

4. **Conclusion.** The surviving hypotheses — $w>0$, $n>0$, $0<p$, $p\le \tfrac1{40w}$, $p\le 1$ — are about $w$, $n$ and $p$ only and are unaffected by cleaning, so they pass through unchanged. Applying `SwitchingBernoulli.switching_bernoulli_dtDepth_cnf` to $\tilde f$ with these data yields exactly
   \[
   \Pr_\rho\big[\operatorname{dtDepth}(\tilde f|_\rho)>t\big]\le\left(\tfrac12\right)^t+\exp\!\left(-\tfrac{np}{3}\right),
   \]
   which, by the identification of events in Step 2, is the claimed bound for $f$. $\qquad\blacksquare$

**Key facts.** `LMN.cleanCNF_eval`, `SwitchingBernoulli.switching_bernoulli_dtDepth_cnf`, `LMN.cleanCNF_width_le`, `LMN.cleanCNF_var_inj`, `LMN.cleanCNF_nodup`.
