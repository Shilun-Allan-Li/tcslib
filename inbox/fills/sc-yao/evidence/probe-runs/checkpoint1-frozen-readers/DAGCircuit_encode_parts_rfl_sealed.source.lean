import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

attribute [local irreducible] BoolCircuit.DAGCircuit.encode

example {n : ℕ} (C : DAGCircuit n) :
    C.encode = encodeNat n ++ (encodeList DAGGate.encode C.gates ++ encodeNat C.output)  := rfl
