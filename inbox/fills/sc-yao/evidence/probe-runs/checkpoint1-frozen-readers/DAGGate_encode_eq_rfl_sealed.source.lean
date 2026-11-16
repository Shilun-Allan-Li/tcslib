import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

attribute [local irreducible] BoolCircuit.DAGGate.encode

example (g : DAGGate) :
    g.encode = g.kind.encode ++ encodeList encodeNat g.args  := rfl
