import os,glob
WT='/home/user/dw10/subB'
EV='/home/user/dw10/sub/snap-r1'
files=[p[len(WT)+1:] for p in glob.glob(WT+'/TCSlib/**/*.lean',recursive=True)]
m={ 'TCSlib/'+p[len('TCSlib/'):-5].replace('/','_'):p for p in files}
mods=set()
for l in open(EV+'/seals/queue.txt'):
    l=l.strip()
    if not l: continue
    t=l.split('/')[-1]; t=t.split('_',1)[1]
    k='TCSlib/'+t
    if k in m: mods.add(m[k])
    else: print('UNMATCHED',l)
open('owners.txt','w').write('\n'.join(sorted(mods))+'\n')
print(len(mods),'owners of',len(files))
