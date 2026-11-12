from pathlib import Path
import subprocess,sys
O=Path('/private/tmp/ab34-ro1-integration');V='/private/tmp/ab34-ro1-native-overlay';B='/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-mac8'
with (O/'owner-queue-attempt8.log').open('wb') as f:q=subprocess.run([sys.executable,'-I',str(O/'run-owners.py')],stdout=f,stderr=subprocess.STDOUT)
print('Final current 60-owner queue exit',q.returncode,flush=True)
if q.returncode:sys.exit(q.returncode)
for name,tree in [('APIInventory.lean',V),('AXCurrent.lean',V),('AXBaseline.lean',B)]:
    q=subprocess.run([sys.executable,'-I',str(O/'run-probe.py'),name,tree,'attempt1','0'])
    if q.returncode:sys.exit(q.returncode)
print('PRIMARY_NATIVE_AND_AX_BATCH_PASS',flush=True)
