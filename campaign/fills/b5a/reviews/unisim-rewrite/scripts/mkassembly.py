# mkassembly.py <overlay> <head-block> <junction-body> <target-body> <out> [seal]
# Inserts the us_ block at the home (the blank line before `end StepBlockClients`) and replaces
# the target's `sorry`; every edit asserted.
import sys
ov,hb,jb,tb,out=sys.argv[1:6]; seal=len(sys.argv)>6
L=open(ov).read().split('\n')
home=8551-1  # overlay line 8551 (0-based index)
assert L[home]=='' and L[home+1]=='end StepBlockClients' and L[home-1].startswith('  exact ⟨T, bound, _, halted, output, summaryClock_accepts'), (L[home-1:home+2])
sorry_i=8664-1
assert L[sorry_i]=='  sorry' and L[8656-1].startswith('theorem exists_uniformSimulator'), L[sorry_i]
SEAL_HOME = open(sys.argv[6]).read() if seal else ''
SEAL_TGT = SEAL_HOME
block=(SEAL_HOME+open(hb).read()+open(jb).read()).rstrip('\n').split('\n')
body=open(tb).read().rstrip('\n').split('\n')
N=L[:sorry_i]+body+L[sorry_i+1:]
if seal:
    # seal again before the target's docstring (after `end StepBlockClients`)
    e=N.index('end StepBlockClients')
    assert N[e+1]=='' and N[e+2].startswith('/-- **The uniform bounded-acceptance simulator**')
    N=N[:e+2]+SEAL_TGT.rstrip('\n').split('\n')+['']+N[e+2:]
N=N[:home+1]+block+['']+N[home+1:]
open(out,'w').write('\n'.join(N))
print('ok', len(N))
