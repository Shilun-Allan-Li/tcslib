import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

example {α : Type} (f : α → List Bool) :
    encodeList f [] = [false]  := rfl
