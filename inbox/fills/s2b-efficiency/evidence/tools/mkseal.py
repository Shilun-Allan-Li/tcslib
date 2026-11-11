import re,os
L='/workspace/exchange/inbox/fills/s2b-efficiency/evidence/logs/seal-scan.log'
rows=[l for l in open(L) if ' | used by ' in l]
seal={}  # module short -> list of names
allregular=[]
for r in rows:
    name,mod,tag,users=[x.strip() for x in r.split(' | ')]
    if not tag.startswith('regular'): continue
    allregular.append(name)
    us=re.findall(r'[\w.]+',users.replace('used by',''))
    for u in us:
        seal.setdefault(u,[]).append(name)
files={'Efficiency.Strings':'TCSlib/Cryptography/Games/Efficiency/Strings.lean',
 'Efficiency.Replay':'TCSlib/Cryptography/Games/Efficiency/Replay.lean',
 'Efficiency.Handler':'TCSlib/Cryptography/Games/Efficiency/Handler.lean',
 'Efficiency.OracleBridge':'TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean',
 'Efficiency.Interactive':'TCSlib/Cryptography/Games/Efficiency/Interactive.lean',
 'Efficiency.InteractiveSpec':'TCSlib/Cryptography/Games/Efficiency/InteractiveSpec.lean',
 'Efficiency':'TCSlib/Cryptography/Games/Efficiency.lean'}
os.makedirs('lean_proof/s2b/seal',exist_ok=True)
summary=[]
for short,path in files.items():
    src=open(path).read()
    names=sorted(set(seal.get(short,[])))
    attr='attribute [local irreducible] '+' '.join('_root_.'+n for n in names)
    # insert after the first 'open ' line following the namespace line
    ns=src.index('\nnamespace ')
    op=src.index('\nopen ',ns) if '\nopen ' in src[ns:] else -1
    if op<0:
        # Replay has no open line: insert after namespace line
        e=src.index('\n',ns+1)
    else:
        e=src.index('\n',op+1)
    hdr='\n\n/-! Seal of the efficiency fill (s2b-efficiency): a verbatim copy of `%s` with every foreign\nnon-reducible TCSlib definition its declarations use made irreducible (scan: `SealScan.lean`). -/\n%s\n'%(path,attr)
    out=src[:e]+hdr+src[e:]
    fn='lean_proof/s2b/seal/Seal'+short.replace('Efficiency.','').replace('Efficiency','Efficiency')+'.lean'
    if short=='Efficiency': fn='lean_proof/s2b/seal/SealEfficiency.lean'
    open(fn,'w').write(out)
    summary.append((short,len(names),fn))
for s in summary: print(*s)
print('regular foreign definitions (sealed somewhere):',len(set(allregular)))
