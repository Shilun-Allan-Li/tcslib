import TCSlib.Complexity.CircuitComplexity.Uniform

open BoolCircuit

attribute [local irreducible] BoolCircuit.encodeList

example {α : Type} (f : α → List Bool) (a : α) (as : List α) :
    encodeList f (a :: as) = true :: (f a ++ encodeList f as)  := rfl
