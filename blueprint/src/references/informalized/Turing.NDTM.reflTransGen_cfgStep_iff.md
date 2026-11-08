<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.reflTransGen_cfgStep_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Runs and Transition Reachability

**Claim.** There is a finite sequence of zero or more choice-dependent single steps from $c$ to $c'$ if and only if some finite Boolean choice word takes the machine from $c$ to $c'$.

**Proof.** For the forward direction, induct on the reflexive-transitive sequence. A sequence of length zero is represented by the empty word. For a sequence extended by one step, the induction hypothesis gives a word $w$ reaching the intermediate configuration, and the final transition is witnessed by a choice bit $b$. Appending $b$ to $w$ represents the whole sequence: the run-concatenation law (`Turing.NDTM.runWith_append`) and the leading-bit run equation (`Turing.NDTM.runWith_cons`), with the empty run law (`Turing.NDTM.runWith_nil`), identify that run with first running $w$ and then taking the witnessed step.

Conversely, induct on a word witnessing the run. The empty word gives the reflexive reachability relation. If the word begins with $b$ and has remainder $w$, the first transition is a single `CfgStep`, witnessed by $b$; by induction, the run under $w$ from the resulting configuration gives a reflexive-transitive sequence to $c'$. Prepending that first step yields the desired reachability.

**Key facts.** `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_nil`.
