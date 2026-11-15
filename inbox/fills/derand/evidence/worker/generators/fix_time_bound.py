from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/TimeBound.lean'
text = path.read_text().replace('open Filter', 'open Filter Topology')
for name in ['tendsto_rpow_neg_atTop', 'tendsto_rpow_atTop', 'isLittleO_log_rpow_atTop']:
    text = text.replace('Real.' + name, name)
path.write_text(text)
