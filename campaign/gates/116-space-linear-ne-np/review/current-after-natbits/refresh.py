"""Current-context source, screen and one-at-a-time Lean validation for gate116.

Git is read-only. Sources are pinned to the parent's successful mlin2 generation.
All outputs stay in this follow-up folder or its own scratch directory.
"""
from pathlib import Path
from collections import Counter
import contextlib
import hashlib
import io
import json
import os
import re
import runpy
import shutil
import subprocess
import sys
import tarfile
import time

H=Path(__file__).resolve().parent
OLD=H.parent
G=OLD.parent
R=H.parents[4]
S=Path(os.environ['TCSLIB_SCRATCH'])
W=S/'linear-consumer-validation/current-after-natbits'
GEN=G/'evidence/current-after-natbits/generation.json'
REL='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'

def commit(ref):
    c=subprocess.check_output(['git','-C',str(R),'rev-parse',ref],text=True).strip()
    subprocess.run(['git','-C',str(R),'cat-file','-e',c+'^{commit}'],check=True)
    return c

def generation():
    d=json.loads(GEN.read_text())
    assert d['exit']==0 and d['expected_changed_lean_files']==1
    d['base']=commit(d['base']);d['head']=commit(d['head'])
    assert d['snapshot']=='oleans-mlin2' and d['previous_snapshot']=='oleans-mac2'
    return d

def parser():
    e=H/'empty.lean.txt';e.write_text('')
    sys.argv=[str(R/'devtools/seyoon/declfreeze.py'),str(e),str(e)]
    with contextlib.redirect_stdout(io.StringIO()):
        chunks=runpy.run_path(sys.argv[0])['chunks']
    header=runpy.run_path(str(OLD/'prepare.py'))['header']
    return chunks,header

def prepare():
    d=generation();W.mkdir(parents=True,exist_ok=True)
    pop=(OLD/'screen/population-head.txt').read_text().splitlines();assert len(pop)==11
    for label in ['base','head']:
        (H/f'population-{label}.txt').write_text('\n'.join(pop)+'\n')
    exports=W/'source-exports';exports.mkdir(exist_ok=True)
    trees={}
    for label in ['base','head']:
        tree=exports/label;assert not tree.exists(), 'preserve an existing export/run'
        tree.mkdir();trees[label]=tree
        p=subprocess.Popen(['git','-C',str(R),'archive',d[label],'--',*pop],stdout=subprocess.PIPE)
        with tarfile.open(fileobj=p.stdout,mode='r|') as archive:
            archive.extractall(tree,filter='data')
        assert p.wait()==0
    diff=subprocess.check_output(['git','-C',str(R),'diff','--name-only',d['base'],d['head'],'--','*.lean'],text=True).splitlines()
    assert diff==[REL],diff
    hashes=[]
    for path in pop:
        row={'path':path}
        for label in ['base','head']:
            data=(trees[label]/path).read_bytes()
            blob=subprocess.check_output(['git','-C',str(R),'rev-parse',d[label]+':'+path],text=True).strip()
            subprocess.run(['git','-C',str(R),'cat-file','-e',blob],check=True)
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob
            row[label+'_git_blob']=blob;row[label+'_sha256']=hashlib.sha256(data).hexdigest()
            dest=H/(label+'-source')/(path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)
        row['changed']=row['base_sha256']!=row['head_sha256']
        assert path==REL or not row['changed']
        hashes.append(row)
    a=(trees['base']/REL).read_text();b=(trees['head']/REL).read_text()
    assert hashlib.sha256(b.encode()).hexdigest()==json.loads((OLD/'source-freeze.json').read_text())['source_sha256']
    assert (S/'wt-epad'/REL).read_bytes()==b.encode()
    chunks,header=parser()
    A={n:(p,t) for n,p,t in chunks(a)};B={n:(p,t) for n,p,t in chunks(b)}
    assert list(A)==list(B)
    assert all(A[n][0]==B[n][0] for n in A)
    assert {n:header(t) for n,(p,t) in A.items()}=={n:header(t) for n,(p,t) in B.items()}
    changed=[n for n in A if A[n][1]!=B[n][1]]
    assert changed==['Complexity.SPACE_linear_ne_NP'],changed
    ia=re.findall(r'^import (.+)$',a,re.M);ib=re.findall(r'^import (.+)$',b,re.M)
    assert [i for i in ib if i not in ia]==['TCSlib.Complexity.SpaceComplexity.Padding']
    assert not [i for i in ia if i not in ib]
    for label,decls in [('base',A),('head',B)]:
        (H/f'headers-{label}.json').write_text(json.dumps({n:header(t) for n,(p,t) in decls.items()},indent=2)+'\n')
    source={'base':d['base'],'head':d['head'],'head_source_sha256':hashlib.sha256(b.encode()).hexdigest(),
        'base_export':str(trees['base']),'head_export':str(trees['head']),
        'source_population':hashes,'changed_lean_files':diff,'changed_source_bodies':changed,
        'source_public_before_after':[4,4],'source_private_before_after':[43,43],
        'base_lines':len(a.splitlines()),'head_lines':len(b.splitlines()),
        'all_headers_visibility_order_unchanged':True,'all_other_declarations_byte_identical':True,
        'approved_import_addition':'TCSlib.Complexity.SpaceComplexity.Padding',
        'same_head_source_content_as_initial_review':True}
    (H/'source-receipt.json').write_text(json.dumps(source,indent=2)+'\n')
    (H/'source.diff').write_text(subprocess.check_output(['git','-C',str(R),'diff',d['base'],d['head'],'--',REL],text=True))
    for name in ['ModuleCensus','AllConstants','Inventory','SimpDefs','Controls-unsealed','Controls-sealed']:
        shutil.copyfile(OLD/(name+'.lean.txt'),H/(name+'.lean.txt'))
    marker='/-- **`SPACE(n + 1) ≠ NP`**';assert b.count(marker)==1 and b.count('\nend Complexity')==1
    sealed=b.replace(marker,'section LinearConsumerSeal\nattribute [local irreducible] Complexity.SPACE Complexity.NP Complexity.padLang Turing.pairEncode\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg\n\n'+marker)
    sealed=sealed.replace('\nend Complexity','\nend LinearConsumerSeal\n\nend Complexity')
    (H/'Hierarchy-sealed.lean.txt').write_text(sealed)
    print(json.dumps({k:source[k] for k in ['base','head','head_source_sha256','base_lines','head_lines']},indent=2))

def screens():
    pins=json.loads((H/'source-receipt.json').read_text());pop=(H/'population-head.txt').read_text().splitlines()
    lock=S/'locks/screen'
    while True:
        try:lock.mkdir();break
        except FileExistsError:time.sleep(5)
    (lock/'pid').write_text(str(os.getpid())+'\n')
    try:
        for label in ['base','head']:
            cmd=['nice','-n','10','python3','-I',str(R/'scripts/copy-text-screen-v3.py'),pins[label+'_export'],*pop]
            start=time.time()
            with (H/f'screen-{label}.txt').open('w') as out:p=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
            data=(H/f'screen-{label}.txt').read_bytes()
            (H/f'screen-{label}-run.json').write_text(json.dumps({'command':cmd,'exit':p.returncode,
                'seconds':time.time()-start,'base':pins['base'],'head':pins['head'],
                'output_sha256':hashlib.sha256(data).hexdigest(),'population_files':len(pop)},indent=2)+'\n')
            assert p.returncode==0
            print(label,data.decode().splitlines()[0],flush=True)
        with (H/'pairdiff.txt').open('w') as out:
            p=subprocess.run(['python3','-I',str(R/'devtools/seyoon/pairdiff.py'),str(H/'screen-head.txt'),str(H/'screen-base.txt')],stdout=out,stderr=subprocess.STDOUT)
        assert p.returncode==0
        print((H/'pairdiff.txt').read_text(),flush=True)
    finally:
        assert (lock/'pid').read_text().strip()==str(os.getpid())
        (lock/'pid').unlink();lock.rmdir()

def checks():
    d=generation();log=S/'fills/replay/replay-mlin2.log'
    data=log.read_bytes();assert data.decode().splitlines()[-1]=='# modules=2 failed=0'
    assert data.decode().splitlines()[0].startswith('# replay-mlin2 at '+d['head'][:8]+':')
    assert (S/d['snapshot']).is_dir()
    (H/'parent-replay.log').write_bytes(data)
    (H/'parent-replay-receipt.json').write_text(json.dumps({'generation':str(GEN.relative_to(R)),
        'base':d['base'],'head':d['head'],'snapshot':d['snapshot'],'modules':2,'failed':0,
        'log_sha256':hashlib.sha256(data).hexdigest(),'run_by_parent_not_this_reviewer':True},indent=2)+'\n')
    runs=[('Census-base','ModuleCensus','oleans-mac2',0,0),
          ('Census-head','ModuleCensus','oleans-mlin2',0,0),
          ('AllConstants-base','AllConstants','oleans-mac2',0,0),
          ('AllConstants-head','AllConstants','oleans-mlin2',0,0),
          ('Inventory','Inventory','oleans-mlin2',0,0),('SimpDefs','SimpDefs','oleans-mlin2',0,0),
          ('Hierarchy-sealed','Hierarchy-sealed','oleans-mlin2',0,0),
          ('Controls-unsealed','Controls-unsealed','oleans-mlin2',0,0),
          ('Controls-sealed','Controls-sealed','oleans-mlin2',1,8)]
    probes=W/'probes';probes.mkdir(exist_ok=True)
    for label,name,olean,expected,errors in runs:
        f=probes/(label+'.lean');f.write_bytes((H/(name+'.lean.txt')).read_bytes())
        cmd=['bash',str(R/'devtools/seyoon/leanelab.sh'),str(S/'wt-epad'),str(S/olean),str(f)]
        start=time.time()
        with (H/(label+'.out')).open('w') as out:p=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT)
        text=(H/(label+'.out')).read_text();actual=text.count('error:')+text.count('error(')
        (H/(label+'-run.json')).write_text(json.dumps({'command':cmd,'base':d['base'],'head':d['head'],
            'input_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'exit':p.returncode,'expected_exit':expected,
            'errors':actual,'expected_errors':errors,'seconds':time.time()-start},indent=2)+'\n')
        print(label,'exit',p.returncode,'errors',actual,flush=True)
        assert p.returncode==expected and actual==errors,(label,text[-1400:])
        if label=='Inventory':
            assert text.count('TARGET ')==2 and 'sorryAx' not in text
            assert 'FOREIGN [Complexity.NP, Complexity.SPACE, Complexity.padLang, Turing.pairEncode]' in text
        if label=='SimpDefs':
            assert text.splitlines()==['Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg','Turing.NDTM.initCfg'],text

if __name__=='__main__':
    mode=sys.argv[1]
    {'prepare':prepare,'screens':screens,'checks':checks}[mode]()
