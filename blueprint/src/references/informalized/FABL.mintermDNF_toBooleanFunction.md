<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.mintermDNF_toBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minterm Representation of a Boolean Function

**Claim.** The disjunctive normal form formed from one minterm for each input where $f$ takes the value $-1$ represents $f$ at every input.

**Proof.** Fix an input $x$. Since the values of $f$ are the two signs, either $f(x)=1$ or $f(x)=-1$. If $f(x)=1$, no minterm in the formula can be satisfied at $x$: each term comes from some input $y$ with $f(y)=-1$, and the minterm characterization says that this term is satisfied at $x$ exactly when $x=y$. Thus the formula evaluates to $1$. If $f(x)=-1$, the minterm indexed by $x$ occurs in the formula, and it is satisfied at $x$ by the same characterization. Hence the formula evaluates to $-1$. In both cases its value agrees with $f(x)$, proving equality of the functions.

**Key facts.** `FABL.DNFTerm.eval_minterm_eq_neg_one_iff`.
