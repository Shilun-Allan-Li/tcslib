from pathlib import Path
root = Path('/Users/seyoonr/.codex/worktrees/derand-proof/tcslib-exchange')
path = root / 'TCSlib/Cryptography/Randomness/Derandomization/Majority.lean'
text = path.read_text()
text = text.replace('import TCSlib.Cryptography.Randomness.Derandomization.CoinGap',
                    'import Mathlib.Data.Rat.Cast.Order\nimport TCSlib.Cryptography.Randomness.Derandomization.CoinGap')
text = text.replace('theorem exists_seed_majority (hPRG', 'open Classical in\ntheorem exists_seed_majority (hPRG')
old = '''    simpa only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      eval_polyLenExpr] using (polyTimeComputable_pairTakePoly (polyLenExpr a k)).comp
        (polyTimeComputable_pairFstD.pairEncode (hF.comp polyTimeComputable_pairSndD))'''
new = '''    convert (polyTimeComputable_pairTakePoly (polyLenExpr a k)).comp
      (polyTimeComputable_pairFstD.pairEncode (hF.comp polyTimeComputable_pairSndD)) using 1
    funext z
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      eval_polyLenExpr]'''
assert old in text
text = text.replace(old, new)
path.write_text(text)
