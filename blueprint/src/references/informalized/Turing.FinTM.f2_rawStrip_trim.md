<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_trim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Trimming Computation

**Claim.** For Boolean words $x,w$ and $i\le |x|$, the designated machine started in state $1$ with work tape $w$, head at $|w|-1$, and empty output halts within $3(|w|+1)$ steps, outputting the prefix before the last true entry, or the empty word if there is no true entry.

**Proof.** Induct on the word by removing its last entry, using the reverse-recursive decomposition into the empty word and a word extended by one bit. For the empty word, choose one step: the machine halts immediately from the relevant blank-cell transition, with empty output, which agrees with the empty-word value of `splitAtLastTrue`. Suppose the word is $w\mathbin{++}[b]$. The first transition is described by the erase lemma (`Turing.FinTM.f2_rawStrip_erase`): it removes the last bit from the work tape and enters state $1$ if $b$ is false, or state $2$ if $b$ is true, with head positioned for the remaining computation. If $b$ is false, apply the induction hypothesis to $w$ and prepend this transition to its run. The bound increases by one and remains below $3(|w\mathbin{++}[b]|+1)$; the definition of `splitAtLastTrue` shows that appending a false bit does not change the selected prefix. If $b$ is true, the machine instead performs the raw-strip completion on $w$: `Turing.FinTM.f2_rawStrip_finish` gives halting with output $w$ after $2(|w|+1)$ further steps. Including the initial erase step gives $2(|w|+1)+1$, within the required bound, and the last true bit makes `splitAtLastTrue (w\mathbin{++}[true])=some\ w$.

**Key facts.** `Turing.FinTM.f2_rawStrip_erase`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.f2_rawStrip_finish`.
