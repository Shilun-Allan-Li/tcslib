import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

attribute [local irreducible] BoolCircuit.encodeList

example {α : Type} (f : α → List Bool) :
    encodeList f [] = [false]  := rfl
