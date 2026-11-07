"""Prepare the pinned MIG-1 overnight fill inputs; no Lean source mutation.

Run with python3 -I after sourcing the scratch environment. The only checked
programs loaded here are the maintainer's declaration parser and graph tools.
"""

from pathlib import Path
import contextlib
import hashlib
import io
import json
import os
import re
import runpy
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
SCRATCH = Path(os.environ['TCSLIB_SCRATCH'])

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], text=True).strip()

def checked(ref):
    sha = git('rev-parse', ref)
    subprocess.run(['git', '-C', str(ROOT), 'cat-file', '-e', sha+'^{commit}'], check=True)
    return sha

def statement(text):
    # A header delimiter is top-level. In particular `input := x` in a
    # parenthesized configuration type is not the theorem's body delimiter.
    out=[];i=0;comment=0;quoted=False;depth=0
    while i<len(text):
        if text.startswith('/-',i) and not quoted:
            comment+=1;i+=2;continue
        if text.startswith('-/',i) and comment:
            comment-=1;i+=2;continue
        if comment:i+=1;continue
        if text.startswith('--',i) and not quoted:
            j=text.find('\n',i);i=len(text) if j<0 else j;continue
        c=text[i]
        if c=='"':quoted=not quoted
        if quoted and c=='\\' and i+1<len(text):
            out.extend(text[i:i+2]);i+=2;continue
        if not quoted:
            if c in '([{⟨':depth+=1
            elif c in ')]}⟩':depth-=1
            if depth==0 and (text.startswith(':=',i) or
                re.match(r'where\b',text[i:]) or c=='|'):
                return ' '.join(''.join(out).split())
        out.append(c);i+=1
    return ' '.join(''.join(out).split())

def main():
    base = checked('83ac315e')
    export = SCRATCH / 'mig1-source' / base
    export.mkdir(parents=True, exist_ok=True)
    proc = subprocess.Popen(['git', '-C', str(ROOT), 'archive', base, 'TCSlib',
                             'TCSlib.lean', 'scripts', 'devtools', 'policy.md',
                             'workflow.md', 'lean-toolchain', 'lake-manifest.json',
                             'lakefile.lean'], stdout=subprocess.PIPE)
    with tarfile.open(fileobj=proc.stdout, mode='r|') as a:
        a.extractall(export, filter='data')
    assert proc.wait() == 0
    # The export is a fresh materialization of this Git tree, not a worktree.
    paths = [
        'TCSlib/Complexity/TuringMachine/Composition.lean',
        'TCSlib/Complexity/TuringMachine/Simulation.lean',
        'TCSlib/Complexity/TuringMachine/Build/Wrappers.lean',
        'TCSlib/Complexity/TuringMachine/Encoding.lean',
        'TCSlib/Complexity/ClassP/TimeConstructible.lean',
        'TCSlib/Complexity/TuringMachine/Build/Loop.lean',
        'TCSlib/Complexity/TuringMachine/Build/Primitives.lean',
        'TCSlib/Complexity/TuringMachine/Build/Catalog.lean',
        'TCSlib/Complexity/TuringMachine/Build/CertShell.lean',
        'TCSlib/Complexity/TuringMachine/CodeSimulator.lean',
        'TCSlib/Complexity/RAMSimulation/WordSize.lean',
    ]
    inp = HERE / 'inputs'
    inp.mkdir(exist_ok=True)
    empty = inp / 'empty.lean.txt'
    empty.write_text('')
    sys.argv = [str(ROOT/'devtools/seyoon/declfreeze.py'), str(empty), str(empty)]
    with contextlib.redirect_stdout(io.StringIO()):
        parser = runpy.run_path(sys.argv[0])
    chunks, stmt = parser['chunks'], statement
    rows, admissions, public = [], [], {}
    for path in paths:
        data = (export/path).read_bytes()
        blob = git('rev-parse', base+':'+path)
        subprocess.run(['git','-C',str(ROOT),'cat-file','-e',blob],check=True)
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == blob
        decls = chunks(data.decode())
        pub = {n: stmt(t) for n, priv, t in decls if not priv}
        public[path] = pub
        rows.append({'path': path, 'git_blob': blob, 'sha256': hashlib.sha256(data).hexdigest(),
                     'lines': len(data.splitlines()), 'public_source': len(pub),
                     'private_source': sum(priv for _,priv,_ in decls)})
        for n, priv, t in decls:
            # Strip comments with the same reviewed parser as the screen.
            no_comments = re.sub(r'/\-.*?\-/', '', t, flags=re.S)
            no_comments = '\n'.join(l.split('--')[0] for l in no_comments.splitlines())
            if re.search(r'\bsorry\b',no_comments):
                admissions.append({'path': path, 'name': n, 'private': priv, 'statement': stmt(t)})
    targets = [a for a in admissions if a['path'] != paths[-1]]
    assert len(targets) == 17, [(a['path'], a['name']) for a in targets]
    assert len(admissions) == 20
    assert not any(a['private'] for a in admissions)
    retired = ['Turing.transferTM_run','Turing.copyTM_run','Turing.clearTM_run',
               'Turing.compareTM_run','Turing.incrementTM_run_succ','Turing.incrementTM_run_overflow']
    assert all(n in public[paths[7]] for n in retired)
    (inp/'owned-files.txt').write_text('\n'.join(paths)+'\n')
    (inp/'source-census.json').write_text(json.dumps({'base':base,'files':rows},indent=2)+'\n')
    (inp/'public-freeze.json').write_text(json.dumps(public,indent=2,sort_keys=True)+'\n')
    (inp/'base-admissions.json').write_text(json.dumps(admissions,indent=2)+'\n')
    (inp/'target-admissions.json').write_text(json.dumps(targets,indent=2)+'\n')
    (inp/'retired-public-names.txt').write_text('\n'.join(retired)+'\n')
    # Full screen populations include every Lean file named in this brief/probe.
    extra = [
        'TCSlib/Complexity/TuringMachine/Configuration.lean',
        'TCSlib/Complexity/TuringMachine/Deterministic.lean',
        'TCSlib/Complexity/TuringMachine/Finite.lean',
        'TCSlib/Complexity/TuringMachine/Build/Convention.lean',
        'TCSlib/Complexity/TuringMachine/Build/Embed.lean',
    ]
    pop = list(dict.fromkeys(paths+extra))
    assert all((export/p).exists() for p in pop)
    (inp/'screen-population.txt').write_text('\n'.join(pop)+'\n')
    mods = {str(p.relative_to(export))[:-5].replace('/', '.'): p
            for p in (export/'TCSlib').rglob('*.lean')}
    imports = {m: re.findall(r'^import\s+(TCSlib\.[\w.]+)', p.read_text(), re.M)
               for m,p in mods.items()}
    cat = 'TCSlib.Complexity.TuringMachine.Build.Catalog'
    prim = 'TCSlib.Complexity.TuringMachine.Build.Primitives'
    # Only the already-approved TCSlib import addition. Validate its direction.
    imports[cat] = list(dict.fromkeys(imports[cat]+[prim]))
    order, seen, active = [], set(), set()
    def visit(m):
        assert m in mods, m
        assert m not in active, ('cycle',m,active)
        if m in seen: return
        active.add(m)
        for dep in sorted(imports[m]): visit(dep)
        active.remove(m)
        seen.add(m)
        order.append(m)
    for p in pop: visit(p[:-5].replace('/','.'))
    (inp/'bootstrap-order.txt').write_text(''.join(m.replace('.','/')+'\n' for m in order))
    roots = set()
    for m in order:
        roots.update(re.findall(r'^import\s+(Mathlib\.[\w.]+)',mods[m].read_text(),re.M))
    roots.add('Mathlib.Algebra.BigOperators.Fin')
    (inp/'mathlib-roots.txt').write_text('\n'.join(sorted(roots))+'\n')
    rev = {}
    for m,deps in imports.items():
        for d in deps: rev.setdefault(d,set()).add(m)
    down, todo = set(), [p[:-5].replace('/','.') for p in paths]
    while todo:
        m=todo.pop()
        if m in down:continue
        down.add(m);todo.extend(rev.get(m,()))
    down.discard('TCSlib')
    dorder=[];dseen=set()
    def dvisit(m):
        if m in dseen:return
        dseen.add(m)
        for dep in sorted(imports[m]):
            if dep in down:dvisit(dep)
        dorder.append(m)
    for m in sorted(down):dvisit(m)
    (inp/'downstream-order.txt').write_text(''.join(m.replace('.','/')+'\n' for m in dorder))
    # A fresh fill host also needs the unaffected imports of affected modules.
    # Keep the small 51-module proof-work bootstrap separate from that complete
    # final sweep, and fetch roots for both before the initial bootstrap.
    order=[];seen=set();active=set()
    for m in sorted(down):visit(m)
    final_order=order.copy()
    (inp/'final-order.txt').write_text(''.join(m.replace('.','/')+'\n' for m in final_order))
    roots=set()
    for m in final_order:
        roots.update(re.findall(r'^import\s+(Mathlib\.[\w.]+)',mods[m].read_text(),re.M))
    roots.add('Mathlib.Algebra.BigOperators.Fin')
    (inp/'mathlib-roots.txt').write_text('\n'.join(sorted(roots))+'\n')
    # Static admission census for the bootstrap and downstream, without claiming
    # any new elaboration. Both lists are regenerated on the delivery by worker.
    base_sorries={}
    for m in final_order:
        names=[]
        for n,_,t in chunks(mods[m].read_text()):
            t=re.sub(r'/\-.*?\-/','',t,flags=re.S)
            t='\n'.join(l.split('--')[0] for l in t.splitlines())
            if re.search(r'\bsorry\b',t):names.append(n)
        if names:base_sorries[m]=names
    (inp/'closure-base-admissions.json').write_text(json.dumps(base_sorries,indent=2)+'\n')
    # Source-side candidate list for all six approved retirements, including docs.
    hits=[]
    pattern=re.compile(r'\b(?:'+ '|'.join(re.escape(n.split('.')[-1]) for n in retired)+r')\b')
    for m,p in sorted(mods.items()):
        for i,line in enumerate(p.read_text().splitlines(),1):
            if pattern.search(line):hits.append(f'{p.relative_to(export)}:{i}: {line}')
    (inp/'retirement-consumers.txt').write_text('\n'.join(hits)+'\n')
    refs=[]
    for ref in ['origin/complexity/arora-barak-ch3-4','origin/lean/dedup-sg1',
                'origin/lean/dedup-natbits','origin/lean/epad-padding-fill']:
        sha=checked(ref)
        changed=git('diff','--name-only',base+'...'+sha,'--','*.lean').splitlines()
        refs.append({'ref':ref,'commit':sha,'owned_overlap':sorted(set(paths)&set(changed))})
    (inp/'open-pr-overlap.json').write_text(json.dumps(refs,indent=2)+'\n')
    meta={'base':base,'export':str(export),'owned_files':len(paths),'target_admissions':len(targets),
          'screen_files':len(pop),'bootstrap_modules':len((inp/'bootstrap-order.txt').read_text().splitlines()),
          'downstream_modules':len(dorder),'final_modules':len(final_order),
          'mathlib_roots':len(roots),'catalog_primitives_edge_acyclic':True}
    (inp/'pins.json').write_text(json.dumps(meta,indent=2)+'\n')
    print(json.dumps(meta,indent=2))

if __name__=='__main__':main()
