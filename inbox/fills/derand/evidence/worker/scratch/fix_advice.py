from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/AdviceGap.lean'
text = path.read_text().replace('f, Set.mem_preimage, pairFstD_pairEncode',
                               'f, Set.preimage, Set.mem_setOf_eq, pairFstD_pairEncode')
text = text.replace('    congr 1\n    · rw [acceptProb_def]',
                    '    congr 1\n    congr 1\n    · rw [acceptProb_def]')
text = text.replace('exact uprob_fst _', 'exact uprob_fst (β := D.Coins s) _')
path.write_text(text)
