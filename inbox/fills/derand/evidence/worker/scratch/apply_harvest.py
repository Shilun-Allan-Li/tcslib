from pathlib import Path

path = Path('TCSlib/Complexity/Randomized/Build/IterateFind.lean')
source = path.read_text()
assert '\ntheorem computesFunInTime_find ' not in source
new = Path('/private/tmp/derand-worker/harvest.lean.txt').read_text()
new = new.replace('      H.tm.runFrom (H.tm.initCfg x) t = Cfg.ofWords anchor '
                  '(stateWord H.k (pairEncode x (init x))) := by',
                  '      H.tm.runFrom (H.tm.initCfg x) t =\n'
                  '        Cfg.ofWords anchor (stateWord H.k (pairEncode x (init x))) := by')
new = new.replace(' := by\n\n  obtain', ' := by\n  -- Build the four clean calls and their shared host.\n  obtain', 1)
new = new.replace('  have hstart :', '  -- Startup copies the input and installs the chosen initial state.\n  have hstart :', 1)
new = new.replace('  have hround :', '  -- A positive round either emits its payload or advances the guarded state.\n  have hround :', 1)
new = new.replace('  have hFuel :', '  -- Pay for binary fuel in the same polynomial budget, then apply the host.\n  have hFuel :', 1)
source = source.replace('\nend Complexity.IterateFind', '\n' + new + '\nend Complexity.IterateFind')
bullet = '''* `Complexity.IterateFind.computesFunInTime_find` — the finite machine with arbitrary
  numerical fuel supplied in binary, a chosen initial state, and an explicit polynomial
  per-round budget.
'''
source = source.replace('## Main results\n\n', '## Main results\n\n' + bullet, 1)
path.write_text(source)
