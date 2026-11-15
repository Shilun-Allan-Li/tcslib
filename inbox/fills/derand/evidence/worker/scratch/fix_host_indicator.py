from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Complexity/Randomized/SeedMajority.lean'
text = path.read_text()
start = text.index('    change M.ComputesInTime x\n')
end = text.index('    by_cases h :', start)
text = text[:start] + text[end:]
text = text.replace('simpa only [if_pos h, decide_eq_true h] using hx',
                    'simpa only [Set.mem_setOf_eq, if_pos h, decide_eq_true h] using hx')
text = text.replace('simpa only [if_neg h, decide_eq_false h] using hx',
                    'simpa only [Set.mem_setOf_eq, if_neg h, decide_eq_false h] using hx')
path.write_text(text)

path = root / 'evidence/tools/check_sorries.py'
text = path.read_text()
old = "    module, number, names = line.split(': ', 2)"
assert old in text
text = text.replace(old, "    if not line.strip() or line.startswith('TOTAL '):\n        continue\n" + old)
path.write_text(text)
