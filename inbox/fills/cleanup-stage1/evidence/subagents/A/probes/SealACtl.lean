import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines

set_option autoImplicit false

-- positive (unsealed): definitional reading works
example (a b : List Bool) :
    Turing.pairEncode a b = (a.flatMap fun b => [b, b]) ++ [false, true] ++ b := rfl

-- positive (sealed, through the reader)
section
attribute [local irreducible] Turing.pairEncode
example (L : ℕ) (w : List Bool) :
    TCSlib.Cryptography.EncodingMachines.padTo L w = (w ++ List.replicate L false).take L :=
  TCSlib.Cryptography.EncodingMachines.padTo_eq L w
-- negative (sealed): must fail exactly once
example (a b : List Bool) :
    Turing.pairEncode a b = (a.flatMap fun b => [b, b]) ++ [false, true] ++ b := rfl
end
