from pathlib import Path
import sys,subprocess
O=Path('/private/tmp/ab34-ro1-integration');V='/private/tmp/ab34-ro1-native-overlay'
for name,expected in [('APIScopeNative.lean',0),('APIScopeSealed.lean',0),('APIControlsNative.lean',0),('APIControlsSealed.lean',1)]:
 q=subprocess.run([sys.executable,'-I',str(O/'run-probe.py'),name,V,'attempt1',str(expected)])
 if q.returncode:sys.exit(q.returncode)
print('API_SCOPE_AND_FRESH_CONTROLS_EXPECTED_OUTCOMES',flush=True)
