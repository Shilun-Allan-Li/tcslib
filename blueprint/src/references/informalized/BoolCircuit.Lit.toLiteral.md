<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/NormalFormConversion.lean :: Lit.toLiteral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Converting a circuit literal to a switching-lemma literal

**Definition.** For `l : BoolCircuit.Lit n`,

```
BoolCircuit.Lit.toLiteral l = ⟨l.idx, !l.sign⟩ : Literal n
```

Both types are a variable index plus one Boolean, but the Boolean means opposite
things: `Lit.sign = true` marks the *positive* literal `xᵢ`, while
`Literal.neg = true` marks the *negated* literal `¬xᵢ`. The conversion therefore
keeps the index and flips the Boolean.

**Remark.** This one field-flip is the whole interface between the circuit
namespace (`Lit`, `Circuit`, `NAndCircuit`, `NOrCircuit`) and the switching-lemma
namespace (`Literal`, `Term`, `DNF`, `CNF`); getting the polarity convention
wrong here would invert every semantics lemma downstream.

**Used in.** `Lit.eval_eq_toLiteral_eval` (the semantic correctness of the
flip), the clause-to-term maps `NAndCircuit.clauseToTerm` /
`NOrCircuit.clauseToTerm` and hence `NOrCircuit.toDNF` / `NAndCircuit.toCNF`,
and the DNF-extraction helpers in `LMN/CircuitHelpers.lean` and
`LMN/CircuitLayerReduction.lean`.
