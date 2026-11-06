# Text-level statement freeze: every non-private declaration header of the base file
# (from its keyword line to ':=') must occur byte-identically in the head file; definition
# bodies (non-theorem decls) must be identical in full; docstrings compared and diffs reported.
import re,subprocess,sys
WT='/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/wt-fill-fac'
P='TCSlib/Cryptography/Candidates/Factoring.lean'
base=subprocess.run(['git','-C',WT,'show','16a7d02d69cae1a700c131e3cc3dd918a7b3d6e1:'+P],capture_output=True,text=True).stdout
head=open(WT+'/'+P).read()
kw=re.compile(r'^(@\[[^\]]*\]\s*)?(private )?(noncomputable )?(theorem|def|abbrev|structure|instance|lemma) (\S+)',re.M)
def decls(s):
    out={}
    ms=list(kw.finditer(s))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(s)
        blk=s[m.start():end]
        # docstring preceding
        pre=s[:m.start()]
        d=pre.rfind('/--'); doc=pre[d:] if d>=0 and pre[d:].rstrip().endswith('-/') else ''
        kind=m.group(4); name=m.group(5)
        cut=re.search(r'\n(?=/--|/-!|-- @|\S)',blk[1:])
        blk=blk[:cut.start()+1] if cut else blk
        priv=bool(m.group(2))
        hdr=blk[:blk.find(':=')] if ':=' in blk else blk
        out[name]=(kind,hdr,blk,doc,priv)
    return out
B=decls(base); H=decls(head)
bad=0
for n,(k,hdr,blk,doc,pv) in B.items():
    if n not in H: print('MISSING',n); bad+=1; continue
    k2,hdr2,blk2,doc2,pv2=H[n]
    if hdr!=hdr2: print('HEADER CHANGED',n); bad+=1
    if k!='theorem' and blk.rstrip()!=blk2.rstrip(): print('BODY CHANGED (non-theorem)',n); bad+=1
    if doc!=doc2: print('DOCSTRING CHANGED',n)
new=[n for n in H if n not in B]
print('base public/total decls:',len(B),' head:',len(H))
print('new declarations:',len(new),' all private:',all(H[n][4] for n in new),' all fac_-prefixed:',all(n.startswith('fac_') for n in new))
print('new:',' '.join(new))
print('RESULT:', 'PASS' if bad==0 else 'FAIL', bad)
