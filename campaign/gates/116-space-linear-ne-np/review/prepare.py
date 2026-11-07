"""Independent gate-116 source checks and probe preparation; no Git mutations."""
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

R=Path(__file__).resolve().parents[4]
H=Path(__file__).resolve().parent
S=Path(os.environ['TCSLIB_SCRATCH'])
WT=S/'wt-epad'
REL='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'

def header(text):
    """Normalize a complete header, stopping only at a top-level body marker."""
    out=[];i=0;comment=0;quoted=False;depth=0
    while i<len(text):
        if text.startswith('/-',i) and not quoted:comment+=1;i+=2;continue
        if text.startswith('-/',i) and comment:comment-=1;i+=2;continue
        if comment:i+=1;continue
        if text.startswith('--',i) and not quoted:
            j=text.find('\n',i);i=len(text) if j<0 else j;continue
        c=text[i]
        if c=='"':quoted=not quoted
        if quoted and c=='\\' and i+1<len(text):out.extend(text[i:i+2]);i+=2;continue
        if not quoted:
            if c in '([{⟨':depth+=1
            elif c in ')]}⟩':depth-=1
            if depth==0 and (text.startswith(':=',i) or re.match(r'where\b',text[i:]) or c=='|'):
                return ' '.join(''.join(out).split())
        out.append(c);i+=1
    return ' '.join(''.join(out).split())

def main():
    H.mkdir(exist_ok=True)
    base=json.loads((H.parent/'evidence/source-base.json').read_text())['base']
    base=subprocess.check_output(['git','-C',str(R),'rev-parse',base],text=True).strip()
    subprocess.run(['git','-C',str(R),'cat-file','-e',base+'^{commit}'],check=True)
    a=subprocess.check_output(['git','-C',str(R),'show',base+':'+REL],text=True)
    b=(WT/REL).read_text()
    assert hashlib.sha256(b.encode()).hexdigest()==json.loads((H.parent/'evidence/source-base.json').read_text())['source_sha256']
    (H/'Hierarchy-base.lean.txt').write_text(a)
    (H/'Hierarchy-head.lean.txt').write_text(b)
    empty=H/'empty.lean.txt';empty.write_text('')
    sys.argv=[str(R/'devtools/seyoon/declfreeze.py'),str(empty),str(empty)]
    with contextlib.redirect_stdout(io.StringIO()):parser=runpy.run_path(sys.argv[0])
    A={n:(p,t) for n,p,t in parser['chunks'](a)}
    B={n:(p,t) for n,p,t in parser['chunks'](b)}
    assert A.keys()==B.keys()
    assert list(A)==list(B)
    assert all(A[n][0]==B[n][0] for n in A)
    changed=[n for n in A if A[n][1]!=B[n][1]]
    assert changed==['Complexity.SPACE_linear_ne_NP'],changed
    for label,decls in [('base',A),('head',B)]:
        (H/f'headers-{label}.json').write_text(json.dumps({n:header(t) for n,(p,t) in decls.items()},indent=2)+'\n')
    assert {n:header(t) for n,(p,t) in A.items()}=={n:header(t) for n,(p,t) in B.items()}
    fixture='theorem test (h : f (input := x) = y) : p := by exact h'
    assert header(fixture)=='theorem test (h : f (input := x) = y) : p'
    imports_a=re.findall(r'^import (.+)$',a,re.M)
    imports_b=re.findall(r'^import (.+)$',b,re.M)
    assert [i for i in imports_b if i not in imports_a]==['TCSlib.Complexity.SpaceComplexity.Padding']
    assert [i for i in imports_a if i not in imports_b]==[]
    census={'base':base,'path':REL,'source_sha256':hashlib.sha256(b.encode()).hexdigest(),
        'base_lines':len(a.splitlines()),'head_lines':len(b.splitlines()),
        'public_source_before':sum(not p for p,t in A.values()),
        'private_source_before':sum(p for p,t in A.values()),
        'public_source_after':sum(not p for p,t in B.values()),
        'private_source_after':sum(p for p,t in B.values()),
        'new_or_removed_source_declarations':[],'changed_declaration_bodies':changed,
        'all_surviving_source_headers_visibility_and_order_unchanged':True,
        'all_other_source_declaration_text_byte_identical':True,
        'added_imports':['TCSlib.Complexity.SpaceComplexity.Padding'],
        'target_header':header(B[changed[0]][1]),
        'header_comparison':'complete top-level-delimited headers; nested input := parser fixture passed',
        'complete_header_files':['headers-base.json','headers-head.json']}
    (H/'source-freeze.json').write_text(json.dumps(census,indent=2)+'\n')
    # Raw lint via the reviewed function, changing only its path-reporting root.
    tool=runpy.run_path(str(R/'scripts/style_lint.py'))
    lint=tool['lint']
    lint.__globals__['ROOT']=H
    for label in ['base','head']:
        fs=lint(H/f'Hierarchy-{label}.lean.txt')
        (H/f'policy-{label}.txt').write_text('\n'.join(fs)+f'\nfindings={len(fs)}\n')
    old=tool['lint'](H/'Hierarchy-base.lean.txt')
    new=tool['lint'](H/'Hierarchy-head.lean.txt')
    # Normalize the known size-only line; all other lint text stays the same.
    norm=lambda ls:[re.sub(r'Hierarchy-(?:base|head)\.lean\.txt','Hierarchy.lean',re.sub(r'\d+ lines \(> 1000, must split\)','SIZE (> 1000, must split)',s)) for s in ls]
    assert norm(old)==norm(new),(old,new)
    # Isolate the changed region. The preceding helper proof is unchanged and
    # same-home; this is intentionally not a seal of the module's legacy body.
    marker='/-- **`SPACE(n + 1) ≠ NP`**'
    assert b.count(marker)==1 and b.count('\nend Complexity')==1
    sealed=b.replace(marker,'section LinearConsumerSeal\nattribute [local irreducible] Complexity.SPACE Complexity.NP Complexity.padLang Turing.pairEncode\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg\n\n'+marker)
    sealed=sealed.replace('\nend Complexity','\nend LinearConsumerSeal\n\nend Complexity')
    (H/'Hierarchy-sealed.lean.txt').write_text(sealed)
    control='''import TCSlib.Complexity.SpaceComplexity.Hierarchy
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Turing Complexity

-- Pointwise controls.
example (s : ℕ → ℕ) : SPACE s =
    {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace L (fun n => c * s n)} := by rfl
example : NP = {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} := by rfl
example (L : Language Bool) (pad : ℕ → ℕ) : padLang L pad =
    {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)} := by rfl
example (x y : List Bool) : pairEncode x y =
    (x.flatMap fun b => [b,b]) ++ [false,true] ++ y := by rfl

-- Parameter-abstracted controls. NP has no parameters: the second control
-- puts its value under a fresh constant-function binder.
example : SPACE = (fun s => {L | ∃ (c : ℕ) (M : FinTM Bool),
    M.DecidesInSpace L (fun n => c * s n)}) := by rfl
example : (fun (_ : Unit) => NP) = (fun _ => {L | ∃ (C c : ℕ) (V : Language Bool), V ∈ P ∧
    ∀ x : List Bool, x ∈ L ↔ ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}) := by rfl
example : padLang = (fun L pad =>
    {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}) := by rfl
example : pairEncode = (fun x y =>
    (x.flatMap fun b => [b,b]) ++ [false,true] ++ y) := by rfl
'''
    (H/'Controls-unsealed.lean.txt').write_text(control)
    (H/'Controls-sealed.lean.txt').write_text(control.replace('open Turing Complexity','open Turing Complexity\nattribute [local irreducible] Complexity.SPACE Complexity.NP Complexity.padLang Turing.pairEncode',1))
    census_probe=(R/'campaign/gates/115-epad-fill/evidence/current/axioms/ModuleCensus-head.lean.txt').read_text().replace('SpaceComplexity.Padding','SpaceComplexity.Hierarchy')
    (H/'ModuleCensus.lean.txt').write_text(census_probe)
    simp_probe=(R/'campaign/gates/115-epad-fill/evidence/current/seal/EPadSimpDefs.lean.txt').read_text().replace('SpaceComplexity.Padding','SpaceComplexity.Hierarchy')
    (H/'SimpDefs.lean.txt').write_text(simp_probe)
    print(json.dumps(census,indent=2))

if __name__=='__main__':main()
