<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: SwitchingLemma.processClauseLits_path_nil_of_rho_none_and_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Empty Remaining Path When a Clause Literal Stays Free

**Claim.** Fix $n$, a list $\mathit{lits}$ of literal–position pairs, a path $\mathit{path}$ given as a list of variable–direction pairs, and two restrictions $\rho_0,\sigma$ on $n$ variables. Suppose the pair $(l,\mathit{idx})$ occurs in $\mathit{lits}$, that every entry of $\mathit{lits}$ whose variable equals $\mathrm{var}(l)$ is equal to $l$, and that $\rho_0$ leaves $\mathrm{var}(l)$ free. Run the lockstep processing of $\mathit{lits}$ against $\mathit{path}$ from $\rho_0,\sigma$, obtaining an updated $\rho_0'$, an updated $\sigma'$, a remaining path, and accumulated auxiliary data. If $\rho_0'$ still leaves $\mathrm{var}(l)$ free, then the remaining path is empty.

**Proof.** **What the processing does.** Recall that $\mathrm{processClauseLits}$ walks $\mathit{lits}$ and $\mathit{path}$ *in lockstep*: at each step it consumes the head literal $(l',\mathit{idx}')$ and the head path entry $(\_,\mathit{dir})$, recurses on the two tails, and in doing so assigns the current literal's variable, replacing $\rho_0$ by $\mathrm{update}(\rho_0,\mathrm{var}(l'),\mathrm{some}\,\mathit{dir})$ (and $\sigma$ correspondingly). The recursion halts the moment either list is exhausted: if the literals run out first the entire remaining path is returned; if the path runs out first the returned remaining path is empty, $[\,]$.

The single external fact we need is a **monotonicity** property of the first restriction component (`processClauseLits_rho_ne_none`): if a variable $v$ is already bound in the input $\rho_0$ (i.e. $\rho_0\,v \neq \mathrm{none}$), then it is still bound in the output $\rho_0'$. This holds because the recursion only ever modifies $\rho_0$ through $\mathrm{update}(\cdot,\cdot,\mathrm{some}\,\cdot)$ — it never erases a binding.

With this in hand the argument is an induction on $\mathit{lits}$, generalising over $\mathit{path}$, $\rho_0$ and $\sigma$ so that the updated restrictions may be fed back in.

1. **Empty literal list.** The hypothesis that $(l,\mathit{idx})$ occurs in $\mathit{lits}$ is impossible when $\mathit{lits}=[\,]$, so this case does not arise.

2. **Nonempty literal list, empty path.** With $\mathit{path}=[\,]$ the processing immediately returns $([\,],\rho_0,\sigma,[\,])$ by definition, so the remaining path is $[\,]$ and there is nothing to prove.

3. **Nonempty literal list $hd::tl$, nonempty path $(\_,\mathit{dir})::ps$.** Unfolding one step, the remaining path of the whole run equals the remaining path of the recursive run on the tails $tl$ and $ps$, started from the updated restrictions $\rho_1 := \mathrm{update}(\rho_0,\mathrm{var}(hd),\mathrm{some}\,\mathit{dir})$ and the corresponding $\sigma_1$. The hypothesis $h$ says that in this recursive run the final $\rho_0'$ still leaves $\mathrm{var}(l)$ free. We split on where $(l,\mathit{idx})$ sits and on how $\mathrm{var}(hd)$ relates to $\mathrm{var}(l)$.

   - **The head is $l$ itself**, i.e. $(l,\mathit{idx})=hd$. Then $\mathrm{var}(hd)=\mathrm{var}(l)$, so the update sets $\rho_1(\mathrm{var}(l))=\mathrm{some}\,\mathit{dir}\neq\mathrm{none}$ — processing $l$ binds its own variable. By monotonicity this binding survives to the end of the recursive run, contradicting $h$. So this case is vacuous.

   - **$l$ lies in the tail $tl$, but $\mathrm{var}(hd)=\mathrm{var}(l)$.** Even though the head literal need not be $l$, it shares $l$'s variable, so again the update gives $\rho_1(\mathrm{var}(l))=\mathrm{some}\,\mathit{dir}\neq\mathrm{none}$. Monotonicity carries this binding to the output, once more contradicting the freeness hypothesis $h$. Vacuous.

   - **$l$ lies in the tail $tl$, and $\mathrm{var}(hd)\neq\mathrm{var}(l)$.** Now the update touches a variable different from $\mathrm{var}(l)$, so $\rho_1(\mathrm{var}(l))=\rho_0(\mathrm{var}(l))=\mathrm{none}$: the variable of $l$ is still free after this step. We may therefore invoke the induction hypothesis on $tl$, $ps$, $\rho_1$, $\sigma_1$. Its premises are met: $(l,\mathit{idx})$ belongs to $tl$; the "same variable forces equality to $l$" condition on $tl$ is the restriction of the one on $hd::tl$; $\rho_1$ leaves $\mathrm{var}(l)$ free as just shown; and $h$ is precisely the freeness of the recursive output. The induction hypothesis then yields that the recursive remaining path — which is the remaining path of the whole run — is $[\,]$.

**Why this says what it says.** The content is that under the stated hypotheses the path must have been *too short to reach $l$*. Were the path long enough, the lockstep walk would eventually consume the entry carrying $l$ (or an earlier entry sharing $l$'s variable) and bind $\mathrm{var}(l)$; monotonicity would keep it bound, contradicting the assumption that $\mathrm{var}(l)$ ends up free. The only consistent possibility is that the path ran out first, and then the remaining path is empty by construction. (The uniqueness hypothesis — that every entry on $\mathrm{var}(l)$ equals $l$ — is threaded through the induction so that the inductive step can even be stated, but notice the terminating contradictions above rely only on a variable being bound, not on which literal did the binding.)

**Key facts.** `SwitchingLemma.processClauseLits_rho_ne_none`.
