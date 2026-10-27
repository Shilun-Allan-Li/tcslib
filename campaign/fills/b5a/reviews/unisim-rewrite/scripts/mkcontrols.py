# mkcontrols.py <ctl1> <ctl2> <seal-attrs> <out>: one control per sealed definition of the review's
# assembly seal, taken from the pre-ship control files' unsealed sections; asserted coverage.
import sys,re
def blocks(p):
    t=open(p).read()
    u=t[t.index('section Unsealed')+len('section Unsealed'):t.index('end Unsealed')]
    out={}
    for b in re.split(r'\n(?=-- )',u.strip()):
        name=b.split('\n',1)[0][3:].strip()
        out[name]=b.strip()
    return out
c={}
for p in sys.argv[1:3]:
    for k,v in blocks(p).items(): c.setdefault(k,v)
seal=open(sys.argv[3]).read()
irr=seal[seal.index('irreducible]')+len('irreducible]'):seal.index('attribute [-simp]')].split()
missing=[n for n in irr if n not in c]
assert not missing, missing
body='\n\n'.join(c[n] for n in irr)
src=f"""import TCSlib.Complexity.TuringMachine.CodeSimulator
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Build.InterpreterStartup

/-! Review controls for the review assembly's seal ({len(irr)} definitions): unsealed every goal
closes; sealed every goal is expected to fail, each at its own goal. -/

namespace Turing

section Unsealed

{body}

end Unsealed

section Sealed

{seal.strip()}

{body}

end Sealed

end Turing
"""
open(sys.argv[4],'w').write(src)
print(len(irr))
