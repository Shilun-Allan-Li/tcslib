-- ROOT-ONLY SEARCH TARGET. No helper proof is supplied here.
-- Append after the current decodeResidues_apply proof in a Classes source prefix.
-- Add `import Lean.Elab.Tactic.LibrarySearch` beside the prefix imports.
-- Do not load the proposed named helper or later admitted Classes theorems.
-- First run exact?; then replace only exact? by apply? and run this same target again.

example (p : ℕ+) (count width : ℕ)
    (word : Fin (count * width) → Bool) (i : Fin count) :
    decodeResidues p count width word i =
      (listToNat (List.ofFn (fun j : Fin width => word (finProdFinEquiv (i, j)))) :
        ZMod (p : ℕ)) := by
  exact?

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
