from pathlib import Path
import json,subprocess,sys
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');P=A/'native-project';V='/private/tmp/ab34-ro1-deterministic-native-overlay';B='/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8'
for name in ['AXSmallAlt','AXSmallBaseline']:
 s=(P/(name+'.lean')).read_text().replace('Turing.bufferedScanCfg_run','Turing.FinTM.bufferedScanCfg_run');(P/(name+'Fixed.lean')).write_text(s);(A/(name+'Fixed.lean.txt')).write_text(s)
rs=json.loads((A/'planned-small-AX-roots.json').read_text());rs[1]['name']='Turing.FinTM.bufferedScanCfg_run';(A/'planned-small-AX-roots-corrected.json').write_text(json.dumps(rs,indent=2)+'\n')
for name,tree,expected in [('AXSmallAltFixed.lean',V,0),('AXSmallBaselineFixed.lean',B,0),('APIScopeNative.lean',V,0),('APIScopeSealed.lean',V,0),('APIControlsNative.lean',V,0),('APIControlsSealed.lean',V,1)]:
 q=subprocess.run([sys.executable,'-I',str(A/'run-probe.py'),name,tree,str(expected)])
 if q.returncode:sys.exit(q.returncode)
print('ALTERNATIVE_BOUNDED_PREFLIGHT_REST_PASS',flush=True)
