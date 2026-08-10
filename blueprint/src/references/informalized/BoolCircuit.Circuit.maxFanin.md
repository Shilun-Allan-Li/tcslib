<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.maxFanin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Maximum fanin of a circuit

**Definition.** `Circuit.maxFanin c : Nat` is the largest number of children of
any gate in `c`, defined by structural recursion: a literal leaf `.lit _` has
fanin `0`, and a gate `.node _ cs` has
`max cs.length (cs.foldr (fun c acc => max c.maxFanin acc) 0)` — its own arity
compared against the recursive maximum over its children.

**Remark.** The gate type `isAnd` is irrelevant, and leaves contribute `0`, so
for a depth-1 circuit `maxFanin` is just the number of literals. It is the
"width" parameter of the circuit class: `maxFanin c ≤ w` says every gate has at
most `w` inputs.

**Used in.** The width hypothesis `hw : c.maxFanin ≤ w` of the LMN
depth-`d`/size-`s`/width-`w` theorems in `BooleanAnalysis/LMN.lean`, and the
`Circuit.maxFanin c ≤ w` bounds carried through `LMN/CircuitHelpers.lean`,
`LMN/CircuitLayerReduction.lean`, and `LMN/RecursiveReduction.lean`, where it
bounds the term width of the DNF extracted from a depth-2 OR gate.
