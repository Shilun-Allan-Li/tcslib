"""Pinned source exports and serialized base/head screens for gate 116.

No Git mutation or proof-worktree edit. Every source is materialized from the
base Git archive; the head export differs only in the reviewed Hierarchy file.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import time

H=Path(__file__).resolve().parent
R=H.parents[3]
S=Path(os.environ['TCSLIB_SCRATCH'])
G=H.parent

def main():
    freeze=json.loads((H/'source-freeze.json').read_text())
    base=subprocess.check_output(['git','-C',str(R),'rev-parse',freeze['base']],text=True).strip()
    subprocess.run(['git','-C',str(R),'cat-file','-e',base+'^{commit}'],check=True)
    pop=[
        'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean',
        'TCSlib/Complexity/SpaceComplexity/Padding.lean',
        'TCSlib/Complexity/SpaceComplexity/Basic.lean',
        'TCSlib/Complexity/ClassNP/NP.lean',
        'TCSlib/Complexity/TuringMachine/Encoding.lean',
        'TCSlib/Complexity/ClassNP/PClosure.lean',
        'TCSlib/Complexity/SpaceComplexity/Constructible.lean',
        'TCSlib/Complexity/TuringMachine/Configuration.lean',
        'TCSlib/Complexity/TuringMachine/Deterministic.lean',
        'TCSlib/Complexity/TuringMachine/Nondeterministic.lean',
        'TCSlib/Complexity/TuringMachine/Finite.lean',
    ]
    out=H/'screen';out.mkdir(exist_ok=True)
    for label in ['base','head']:
        (out/f'population-{label}.txt').write_text('\n'.join(pop)+'\n')
    exports=S/'linear-consumer-validation/source-exports'
    exports.mkdir(exist_ok=True)
    before=exports/'base';after=exports/'head'
    assert not before.exists() and not after.exists(), 'source exports already exist; preserve the existing run'
    before.mkdir()
    p=subprocess.Popen(['git','-C',str(R),'archive',base,'--',*pop],stdout=subprocess.PIPE)
    with tarfile.open(fileobj=p.stdout,mode='r|') as archive:
        archive.extractall(before,filter='data')
    assert p.wait()==0
    shutil.copytree(before,after)
    changed=pop[0]
    actual=(S/'wt-epad'/changed).read_bytes()
    assert hashlib.sha256(actual).hexdigest()==freeze['source_sha256']
    (after/changed).write_bytes(actual)
    hashes=[]
    for path in pop:
        blob=subprocess.check_output(['git','-C',str(R),'rev-parse',base+':'+path],text=True).strip()
        subprocess.run(['git','-C',str(R),'cat-file','-e',blob],check=True)
        a=(before/path).read_bytes();b=(after/path).read_bytes()
        assert hashlib.sha1(b'blob '+str(len(a)).encode()+b'\0'+a).hexdigest()==blob
        assert path==changed or a==b
        hashes.append({'path':path,'base_git_blob':blob,'base_sha256':hashlib.sha256(a).hexdigest(),
                       'head_sha256':hashlib.sha256(b).hexdigest(),'changed':a!=b})
        target=out/'base-source'/(path+'.txt')
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(a)
    receipt={'base':base,'head_source_sha256':freeze['source_sha256'],
             'head_pr_commit':'pending parent PR publication','base_export':str(before),
             'head_export':str(after),'source_population':hashes,
             'head_export_changes_from_base':[x['path'] for x in hashes if x['changed']]}
    (out/'source-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    lock=S/'locks/screen'
    while True:
        try:lock.mkdir();break
        except FileExistsError:time.sleep(5)
    (lock/'pid').write_text(str(os.getpid())+'\n')
    try:
        for label,tree in [('base',before),('head',after)]:
            cmd=['nice','-n','10','python3','-I',str(R/'scripts/copy-text-screen-v3.py'),str(tree),*pop]
            start=time.time()
            with (out/f'screen-{label}.txt').open('w') as log:
                run=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
            data=(out/f'screen-{label}.txt').read_bytes()
            (out/f'screen-{label}-run.json').write_text(json.dumps({'command':cmd,
                'base':base,'label':label,'exit':run.returncode,'seconds':time.time()-start,
                'source_receipt':'source-receipt.json','output_sha256':hashlib.sha256(data).hexdigest()},indent=2)+'\n')
            assert run.returncode==0
            print(label,data.decode().splitlines()[0],flush=True)
        cmd=['python3','-I',str(R/'devtools/seyoon/pairdiff.py'),str(out/'screen-head.txt'),str(out/'screen-base.txt')]
        with (out/'pairdiff.txt').open('w') as log:
            q=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT)
        assert q.returncode==0
        print((out/'pairdiff.txt').read_text(),flush=True)
    finally:
        assert (lock/'pid').read_text().strip()==str(os.getpid())
        (lock/'pid').unlink();lock.rmdir()

if __name__=='__main__':main()
