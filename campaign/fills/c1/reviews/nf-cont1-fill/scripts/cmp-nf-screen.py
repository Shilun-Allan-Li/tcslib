# cmp-nf-screen.py: the restricted head screen against the worker's after screen and the screen base,
# on the pair lines with an NDNormalForm declaration on either side.
import re
S='/private/tmp/claude-501/-Users-seyoonr-phd-experiments-tcslib/8f0076bc-454a-4666-b8cf-f4c7ed13c549/scratchpad'
R=S+'/review/nf-cont1-fill'; X=S+'/intake/c1-nf-cont1/x/fill-c1-nf-cont1'
def pairs(f):
    out=set()
    for l in open(f,encoding='utf-8'):
        m=re.match(r'\s+(\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%', l)
        if m and ('NDNormalForm' in m.group(1) or 'NDNormalForm' in m.group(2)): out.add(m.groups())
    return out
mine=pairs(R+'/out/20-screen-nf.txt'); work=pairs(X+'/evidence/screens/screen-after.txt')
base=pairs(S+'/wt-hk/campaign/fills/c1/logs/c1-fill-nf-cont1-screen-base.txt')
print('summary line:', open(R+'/out/20-screen-nf.txt',encoding='utf-8').readline().strip())
print('NDNormalForm pairs: mine', len(mine), '| worker after screen', len(work), '| screen base', len(base))
print('mine == worker:', mine==work)
print('in mine, not the worker\'s:', sorted(mine-work)); print('in the worker\'s, not mine:', sorted(work-mine))
new=mine-base
print('new against the base:', len(new), '| removed:', sorted(base-mine))
print('characters reproduced in the new pairs:', sum(int(p[2]) for p in new))
