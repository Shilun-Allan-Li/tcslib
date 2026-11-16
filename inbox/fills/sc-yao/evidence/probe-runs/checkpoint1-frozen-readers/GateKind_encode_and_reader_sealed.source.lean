import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

attribute [local irreducible] BoolCircuit.GateKind.encode

example : GateKind.encode .and = [false, false]  := BoolCircuit.GateKind.encode_and
