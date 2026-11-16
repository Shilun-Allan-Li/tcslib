import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

example (g : DAGGate) :
    g.encode = g.kind.encode ++ encodeList encodeNat g.args  := rfl
