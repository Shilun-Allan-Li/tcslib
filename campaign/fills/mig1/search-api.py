"""Enumerate current forwarding-map API names/shapes across available refs.

This is candidate enumeration plus source inspection, never an exhaustiveness
proof. No checkout, fetch, source edit or Lean execution is performed.
"""
from pathlib import Path
import contextlib
import io
import json
import re
import runpy
import subprocess
import sys

h=Path(__file__).resolve().parent;r=h.parents[2];out=h/'inputs/search';out.mkdir(exist_ok=True)
def git(*args):return subprocess.check_output(['git','-C',str(r),*args],text=True).strip()
prefixes=('refs/heads/lean/','refs/remotes/origin/lean/','refs/deliver/',
          'refs/heads/deliver/','refs/remotes/origin/deliver/',
          'refs/heads/archive/mac/','refs/remotes/origin/archive/mac/')
refs=[x for x in git('for-each-ref','--format=%(refname)').splitlines() if x.startswith(prefixes)]
refs+=['origin/complexity/arora-barak-ch3-4','83ac315e']
for p in json.loads((h/'inputs/open-prs.json').read_text()):
    refs+=['origin/'+p['headRefName']]
by_tree={};receipt=[]
for ref in sorted(set(refs)):
    sha=git('rev-parse',ref)
    subprocess.run(['git','-C',str(r),'cat-file','-e',sha+'^{commit}'],check=True)
    tree=git('rev-parse',sha+':TCSlib')
    subprocess.run(['git','-C',str(r),'cat-file','-e',tree+'^{tree}'],check=True)
    receipt.append({'ref':ref,'commit':sha,'tcslib_tree':tree})
    by_tree.setdefault(tree,sha)
pattern=r'pairMapSndTM|fwdMapTM|a2_mapTM|pairMapSnd_spaceUsed|pairEncode.*\([a-zA-Z_][a-zA-Z_0-9]* [a-zA-Z_][a-zA-Z_0-9]*\)'
sys.argv=[str(r/'devtools/seyoon/declfreeze.py'),str(h/'inputs/empty.lean.txt'),str(h/'inputs/empty.lean.txt')]
with contextlib.redirect_stdout(io.StringIO()):parser=runpy.run_path(sys.argv[0])
names={'Turing.FinTM.pairMapSndTM','Turing.FinTM.pairMapSndTM_computes','Turing.FinTM.pairMapSndTM_spaceUsed'}
hits={};collisions=[]
for tree,sha in by_tree.items():
    p=subprocess.run(['git','-C',str(r),'grep','-n','-E',pattern,sha,'--','TCSlib'],text=True,capture_output=True)
    assert p.returncode in (0,1),p.stderr
    (out/(sha+'.txt')).write_text(p.stdout)
    rows=p.stdout.splitlines();hits[sha]={'tree':tree,'candidate_lines':len(rows)}
    files={line.split(':',2)[1] for line in rows}
    for path in sorted(files):
        text=git('show',sha+':'+path)
        for n,private,body in parser['chunks'](text):
            if n in names and not private:
                collisions.append({'commit':sha,'path':path,'name':n})
(out/'refs.json').write_text(json.dumps(receipt,indent=2)+'\n')
(out/'summary.json').write_text(json.dumps({'ref_count':len(receipt),'unique_tcslib_trees':len(by_tree),
    'pattern':pattern,'trees':hits,'public_name_candidates':collisions,
    'method':'Candidate enumeration, followed by declaration-kind/name inspection; not an exhaustive semantic duplication proof.'},indent=2)+'\n')
print('Searched',len(receipt),'refs /',len(by_tree),'distinct TCSlib trees; public-name candidates:',len(collisions))
for c in collisions:print(c)
