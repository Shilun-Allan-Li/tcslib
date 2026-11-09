from pathlib import Path
import subprocess,sys
B=Path(__file__).resolve().parent
for label,file in [('05-EXP-full-boundary','EXPFullBoundary.lean'),('06-XR-full-boundary','ExhaustiveReplayFullBoundary.lean'),('07-Hardness-full-boundary','HardnessFullBoundary.lean'),('08-InputCall-full-boundary','InputCallFullBoundary.lean')]:
    subprocess.run([sys.executable,'-I',str(B/'run-check.py'),label,file,'Exact passed full owner source; all touched declaration headers/bodies sealed at every captured ordinary foreign definition head; no projection guards'],check=True)
