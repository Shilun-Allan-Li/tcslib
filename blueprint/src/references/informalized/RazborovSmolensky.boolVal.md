<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: boolVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The field value of a single bit

**Definition.** For `b : Fin 2`,

`boolVal p b = ((b : Nat) : ZMod p)`,

i.e. `0 ↦ 0` and `1 ↦ 1` in `ZMod p`.

**Remark.** A deliberately minimal wrapper for the one-bit cast, so that the two
facts the circuit induction needs about it can be stated as lemmas:
`boolVal_mem` (the value lies in `{0, 1}`) and `bitify_boolVal` (`bitify` inverts
it). `boolInput` is the same cast applied coordinatewise to an input vector.

**Used in.** `boolVal_mem` and `bitify_boolVal` only; those two are then applied
inside `stepLayerFamily`, where circuit node values `F.evalNode … x : Fin 2` are
cast into `ZMod p`.
