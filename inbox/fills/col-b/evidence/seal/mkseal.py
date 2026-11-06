W='/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/fillwork-col-b/'
WT='/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/wt-fill-col-b/'
names=[l.strip() for l in open(W+'seal/names2.txt') if l.strip()]
def seal(excl=()):
    return '\n'.join('attribute [local irreducible] '+n for n in names if n not in excl)+'\n'
ctrl='''/-- Seal control: `edgeIdxOfMsg` read through its body (must FAIL sealed, PASS unsealed). -/
example (m : ℕ) (w : List Bool) : TCSlib.Cryptography.edgeIdxOfMsg m w = w.length % m := rfl
/-- Seal control: `msgAt` read through its body (must FAIL sealed, PASS unsealed). -/
example (w : List Bool) (i : ℕ) : TCSlib.Cryptography.msgAt w i = Complexity.pairFstD (Complexity.pairSndD^[i] w) := rfl
'''
base='TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/'
for mod,anchor,excl in [('ColZKLemmas','open Complexity Turing\n',()),('ColZKMachine','open Complexity Turing\n',('TCSlib.Cryptography.ColSimLemmas.mergeAt',))]:
    s=open(WT+base+mod+'.lean').read()
    assert s.count(anchor)==1
    for tag,blk in [('sealed',seal(excl)+ctrl),('unsealed',ctrl)]:
        open(W+'seal/%s_%s.lean'%(mod,tag),'w').write(s.replace(anchor,anchor+'\n'+blk+'\n'))
s=open(WT+base+'Simulator.lean').read()
v='variable {Com : List Bool → List Bool} {ℓ : PolyExpr}\n'
a1='/-- **The colour-pair sampler is within `(1/4)^T` of a uniform distinct pair**'
a2='/-- One attempt of the string simulator [PS10, Algorithm 128.7, steps 1–4]'
assert s.count(a1)==1 and s.count(a2)==1
for tag,blk in [('sealed',seal()+ctrl),('unsealed',ctrl)]:
    t=s.replace(a1,'section ColZKStep1\n'+blk+'\n'+a1).replace(a2,'end ColZKStep1\n\n'+a2)
    assert t.count(v)==2
    t=t.replace(v,v+'\n'+blk+'\n')
    open(W+'seal/Simulator_%s.lean'%tag,'w').write(t)
