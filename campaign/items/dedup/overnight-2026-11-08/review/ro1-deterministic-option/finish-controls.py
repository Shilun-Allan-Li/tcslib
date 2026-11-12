from pathlib import Path
import subprocess,sys,json
A=Path('/private/tmp/ab34-ro1-deterministic-home-proposal');P=A/'native-project';V='/private/tmp/ab34-ro1-deterministic-native-overlay'
old='''            | .const ``Turing.FinTM _ =>
              lhs := mkProj ``Turing.FinTM 0 lhs
              rhs := mkProj ``Turing.FinTM 0 rhs
'''
for label in ['Native','Sealed']:
 s=(P/('APIControls'+label+'.lean')).read_text();assert s.count(old)==1;s=s.replace(old,'');(P/('APIControls'+label+'Fixed.lean')).write_text(s);(A/('APIControls'+label+'Fixed.lean.txt')).write_text(s)
for name,expected in [('APIControlsNativeFixed.lean',0),('APIControlsSealedFixed.lean',1)]:
 q=subprocess.run([sys.executable,'-I',str(A/'run-probe.py'),name,V,str(expected)])
 if q.returncode:sys.exit(q.returncode)
print('ALTERNATIVE_FRESH_CONTROLS_EXPECTED_OUTCOMES',flush=True)
