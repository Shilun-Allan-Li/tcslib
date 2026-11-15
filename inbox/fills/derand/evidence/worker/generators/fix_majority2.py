from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/Majority.lean'
text = path.read_text().replace('open Classical in\ntheorem exists_seed_majority',
                               'theorem exists_seed_majority')
text = text.replace('/-- A BPP language is the strict seed-majority language',
                    'open Classical in\n/-- A BPP language is the strict seed-majority language')
text = text.replace('        exact_mod_cast (hcorrect x).1 hx',
'''        rw [show (2 : ℝ) / 3 = ((2 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
        exact (hcorrect x).1 hx''')
text = text.replace('      exact_mod_cast hhalf',
'''      apply (Rat.cast_lt (K := ℝ)).mp
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hhalf''')
text = text.replace('''        exact_mod_cast (show Randomized.randProb (Randomized.polyLen a k x.length)
          (fun r => M x r = true) ≤ (1 / 3 : ℚ) by linarith)''',
'''        rw [show (1 : ℝ) / 3 = ((1 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
        linarith''')
text = text.replace('        exact_mod_cast hx',
'''        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
          (Rat.cast_lt (K := ℝ)).mpr hx''')
text = text.replace('  change x ∈ L ↔ _',
'''  change x ∈ L ↔ 2 ^ w x.length <
    2 * (Finset.univ.filter fun u : Fin (w x.length) → Bool =>
      pairEncode x (List.ofFn u) ∈ V).card''')
path.write_text(text)
