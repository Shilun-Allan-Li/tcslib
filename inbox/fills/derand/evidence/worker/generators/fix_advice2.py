from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean'
text = path.read_text()
old = '''  simpa only [Randomized.boolVerifier_apply, f, Set.preimage, Set.mem_setOf_eq, pairFstD_pairEncode]
    using hV x (C (pairEncode x r))'''
new = '''  change
    (Randomized.boolVerifier (fun x r => M x (C (pairEncode x r))) x r = some true ↔
      f (pairEncode x r) ∈ V₁) ∧
    (Randomized.boolVerifier (fun x r => M x (C (pairEncode x r))) x r = some false ↔
      f (pairEncode x r) ∈ V₀)
  simpa only [Randomized.boolVerifier_apply, f, pairFstD_pairEncode]
    using hV x (C (pairEncode x r))'''
assert old in text
text = text.replace(old, new)
text = text.replace('      exact uprob_fst (β := D.Coins s) _',
'''      exact uprob_fst (α := Fin s → Bool) (β := D.Coins s)
        (fun r => M (xs s) (List.ofFn (G.G s r)) = true)''', 1)
text = text.replace('      exact uprob_fst (β := D.Coins s) _',
'''      exact uprob_fst (α := Fin (G.stretch.eval s) → Bool) (β := D.Coins s)
        (fun r => M (xs s) (List.ofFn r) = true)''', 1)
path.write_text(text)
