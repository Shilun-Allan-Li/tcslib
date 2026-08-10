<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: cnfToDualDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The De Morgan dual of a CNF

**Definition.** `cnfToDualDNF ψ` is the `DNF n` obtained from a `CNF n` by
negating every literal in place, leaving the list-of-lists shape untouched:
`ψ.map (fun clause => clause.map Literal.flipNeg)`. Since both `CNF n` and
`DNF n` are the same abbreviation `List (Term n) = List (List (Literal n))`,
this is literally a double `List.map`; the change of meaning is entirely in the
reading — each clause (an OR) is reinterpreted as a term (an AND) — realising
`¬(⋀ᵢ ⋁ⱼ lᵢⱼ) = ⋁ᵢ ⋀ⱼ ¬lᵢⱼ`.

**Used in.** The dual's basic properties are `cnfToDualDNF_width`
(`(cnfToDualDNF ψ).width = ψ.width`, since `Literal.flipNeg` does not change
list lengths) and `cnfToDualDNF_eval`
(`(cnfToDualDNF ψ).eval x = !(ψ.eval x)`, by `Bool.not_and` / `Bool.not_or`
induction), plus `cnfToDualDNF_nodup` and `cnfToDualDNF_inj` transporting
per-clause hygiene hypotheses (`Literal.flipNeg` is injective and preserves
`Literal.var`). These let the `SwitchingLemmaCNF` results reduce a CNF
switching statement to the DNF one already proved, negation being invisible to
the decision-tree depth `dtDepth`.
