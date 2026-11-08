from pathlib import Path
import json,subprocess,sys
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');V='/private/tmp/ab34-ro1-deterministic-native-overlay';C='/private/tmp/ab34-ro1-native-overlay';B='/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8'
for p in json.loads((A/'planned-native-owners.json').read_text())[1:]:
 q=subprocess.run([sys.executable,'-I',str(A/'run-owner.py'),p,'attempt1'])
 if q.returncode:sys.exit(q.returncode)
for name,tree,expected in [('APITypeCfg.lean',C,0),('APITypeDet.lean',V,0),('AXSmallAlt.lean',V,0),('AXSmallBaseline.lean',B,0),('APIScopeNative.lean',V,0),('APIScopeSealed.lean',V,0),('APIControlsNative.lean',V,0),('APIControlsSealed.lean',V,1)]:
 q=subprocess.run([sys.executable,'-I',str(A/'run-probe.py'),name,tree,str(expected)])
 if q.returncode:sys.exit(q.returncode)
print('BOUNDED_ALTERNATIVE_PREFLIGHT_EXPECTED_OUTCOMES',flush=True)
