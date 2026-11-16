import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

attribute [local irreducible] BoolCircuit.GateKind.encode

example : GateKind.encode .not = [true, false]  := rfl
