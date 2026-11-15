from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority/Words.lean'
text = path.read_text().replace('(by simpa using Nat.sub_le m (Nat.bits i).length)', '(by simp)')
text = text.replace('Finset.range_succ', 'Finset.range_add_one')
old = '''  · rw [if_pos h, if_pos h, Finset.card_insert_of_not_mem]
    · omega
    · intro hi
      exact (Nat.lt_irrefl i) (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)'''
new = '''  · have hnot : i ∉ (Finset.range i).filter (fun j => pairEncode x (word m j) ∈ V) := by
      intro hi
      exact (Nat.lt_irrefl i) (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    rw [if_pos h, if_pos h, Finset.card_insert_of_notMem hnot]'''
assert old in text
text = text.replace(old, new)
old = '''    have hi : i < 2 ^ m := ((Randomized.bitsEquiv m) u).isLt
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, ?_⟩
    · have hword : word m i = List.ofFn u := by
        simpa only [Fin.eta, Equiv.symm_apply_apply] using word_eq_ofFn m i hi
      rw [hword]
      exact (Finset.mem_filter.mp hu).2
    · exact (Randomized.bitsEquiv m).symm_apply_apply u'''
new = '''    have hi : i < 2 ^ m := ((Randomized.bitsEquiv m) u).isLt
    have hiFin : (⟨i, hi⟩ : Fin (2 ^ m)) = (Randomized.bitsEquiv m) u := by
      apply Fin.ext
      rfl
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩, ?_⟩
    · rw [word_eq_ofFn m i hi, hiFin, Equiv.symm_apply_apply]
      exact (Finset.mem_filter.mp hu).2
    · rw [hiFin, Equiv.symm_apply_apply]'''
assert old in text
text = text.replace(old, new)
path.write_text(text)
