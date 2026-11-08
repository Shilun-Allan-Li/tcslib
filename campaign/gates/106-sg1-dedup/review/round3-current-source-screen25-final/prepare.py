"""Adopt the executed25-file BASE exactly; capture a fresh63a3 HEAD, no tiling."""
from pathlib import Path
import base64, datetime, hashlib, io, json, os, subprocess, tarfile, tempfile

ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OLD=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25'
OUT=OLD.parent/'round3-current-source-screen25-final'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def pin(ref):
    value=git('rev-parse',ref+'^{commit}').decode().strip()
    assert git('cat-file','-t',value).strip()==b'commit'
    return value
def save(name,value):(OUT/name).write_text(json.dumps(value,indent=2,ensure_ascii=False)+'\n')

old=json.loads((OLD/'capture.json').read_text())
base=pin(old['base']);head=pin('63a3ce018e96c8c114b9c82f8d5fce6021c7d03c')
previous_head=pin(old['head']);campaign=pin('8eb2a60e9')
assert base=='3023dc1408c3d216fc07a7cbba9ae30135b861ed'
assert previous_head=='d0c4a292e781b55617e05b33fdd423bb059fd735'
population=(OLD/'population.txt').read_text().splitlines()
assert len(population)==len(set(population))==25 and population==list(old['population'])
assert sha((OLD/'SHA256SUMS').read_bytes())=='e1570fd0d551aaa512e6563fba2a28e34624caac00a45dc31fe1bc66cffa3f91'
manifest_files=[]
for line in (OLD/'SHA256SUMS').read_text().splitlines():
    digest,path=line.split('  ',1);assert sha((OLD/path).read_bytes())==digest;manifest_files.append(path)
extra_old_files=sorted(str(p.relative_to(OLD)) for p in OLD.rglob('*') if p.is_file() and p.name!='SHA256SUMS' and str(p.relative_to(OLD)) not in manifest_files)
tool='scripts/copy-text-screen-v3.py';toolbytes=(ROOT/tool).read_bytes()
assert sha(toolbytes)==old['tools'][tool]=='f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181'
for commit in [base,head,campaign]:assert git('show',commit+':'+tool)==toolbytes
oldrun=json.loads((OLD/'base-run.json').read_text());raw=(OLD/'base.out').read_bytes()
assert oldrun['exit']==0 and oldrun['full_population']==25 and oldrun['command'][7:]==population
assert oldrun['script_sha256']==sha(toolbytes) and oldrun['output_sha256']==sha(raw) and len(raw)==oldrun['bytes']
assert oldrun['first_line']=='declarations screened: 1956; copy pairs (target reproduces >= half of source): 2013; reproduced text: 646,340 chars'
assert git('diff','--name-only',base,campaign,'--','*.lean')==b''
changed=git('diff','--name-only',base,head,'--','*.lean').decode().splitlines()
assert sorted(changed)==sorted(old['changed_files']) and len(changed)==5
assert git('diff','--name-only',previous_head,head,'--','*.lean').decode().splitlines()==['TCSlib/Complexity/CookLevin/Hardness.lean']
OUT.mkdir(exist_ok=False)
(OUT/'prepare.py').write_bytes(Path(__file__).read_bytes())
scratch=Path(tempfile.mkdtemp(prefix='tcslib106-final25-',dir='/private/tmp'))
capture=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=base,head=head,
    previous_head=previous_head,campaign=campaign,population=old['population'],changed_files=changed,
    temporary_trees={},sides={},tools={tool:sha(toolbytes)},baseline_mode='ADOPTED actual prior executed BASE; no new BASE tiling')
for side,commit in [('base',base),('head',head)]:
    archive=base64.b64decode((OLD/'base.tar.base64.txt').read_bytes()) if side=='base' else git('archive','--format=tar',commit,'--',*population)
    (OUT/(side+'.tar.base64.txt')).write_bytes(base64.encodebytes(archive))
    tree=scratch/side;tree.mkdir();rows=[]
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        members=[m for m in tar.getmembers() if m.isfile()]
        assert sorted(m.name for m in members)==sorted(population)
        for member in members:
            path=member.name;data=tar.extractfile(member).read();blob=git('rev-parse',commit+':'+path).decode().strip()
            assert git('cat-file','blob',blob)==data
            assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==blob
            if side=='base':
                row=next(r for r in old['sides']['base']['files'] if r['path']==path)
                assert data==(OLD/'inputs/base'/(path+'.txt')).read_bytes()==git('show',campaign+':'+path)
                assert sha(data)==row['sha256'] and blob==row['blob']
            target=tree/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
            inert=OUT/'inputs'/side/(path+'.txt');inert.parent.mkdir(parents=True,exist_ok=True);inert.write_bytes(data)
            rows.append(dict(path=path,blob=blob,bytes=len(data),lines=len(data.splitlines()),sha256=sha(data)))
    capture['temporary_trees'][side]=str(tree)
    capture['sides'][side]=dict(archive_bytes=len(archive),archive_sha256=sha(archive),files=rows)
for name in ['base.out','base-run.json','base-request.json']:(OUT/name).write_bytes((OLD/name).read_bytes())
(OUT/'population.txt').write_bytes((OLD/'population.txt').read_bytes())
(OUT/'changed-files.txt').write_text('\n'.join(changed)+'\n')
(OUT/'tools').mkdir();(OUT/'tools/copy-text-screen-v3.py.txt').write_bytes(toolbytes)
save('capture.json',capture)
save('baseline-adoption.json',dict(adopted_utc=capture['created_utc'],source_generation=str(OLD.relative_to(ROOT)),
    old_manifest_sha256=sha((OLD/'SHA256SUMS').read_bytes()),old_verified_manifest_entries=len(manifest_files),old_extra_files=extra_old_files,
    original_execution=oldrun,output_sha256=sha(raw),base=base,current_campaign=campaign,
    all_campaign_Lean_equal_base=True,all25_source_blobs_and_archives_exact=True,tool_exact=True,population_bytes_exact=True,
    baseline_rerun=False,scope='Actual executed BASE875.403s at recorded original times adopted; original raw command/receipt copied verbatim. No newly executed BASE is claimed.'))
save('tool-provenance.json',dict(tool=tool,sha256=sha(toolbytes),equal_BASE_HEAD_campaign_Git=True,inert_copy='tools/copy-text-screen-v3.py.txt'))
(OUT/'base-to-final-source.diff').write_bytes(git('diff','--no-ext-diff','--no-color',base,head,'--','*.lean'))
(OUT/'previous-to-final-source.diff').write_bytes(git('diff','--no-ext-diff','--no-color',previous_head,head,'--','*.lean'))
save('source-progression.json',dict(base=base,previous_head=previous_head,head=head,campaign=campaign,
    all_Lean_base_to_campaign_empty=True,previous_to_final_only=['TCSlib/Complexity/CookLevin/Hardness.lean'],
    source_rows=[dict(path=r['path'],previous_sha256=next(a for a in old['sides']['head']['files'] if a['path']==r['path'])['sha256'],final_sha256=r['sha256']) for r in capture['sides']['head']['files']]))
wt=Path(os.environ['TCSLIB_SCRATCH'])/'wt-sg1'
wt_head=subprocess.run(['git','-C',str(wt),'rev-parse','HEAD'],check=True,stdout=subprocess.PIPE).stdout.decode().strip()
wt_dirty=subprocess.run(['git','-C',str(wt),'diff','--name-only','HEAD','--','*.lean'],check=True,stdout=subprocess.PIPE).stdout.decode()
assert wt_head==head and wt_dirty==''
save('live-source-readonly.json',dict(worktree=str(wt),head=wt_head,all_uncommitted_Lean_diff=wt_dirty,scope='Read-only HEAD/Lean-tree check; no Git mutation.'))
runner=(OLD/'run-screens.py').read_text()
assert runner.count("for side in ['base', 'head']:")==1
runner=runner.replace("for side in ['base', 'head']:","for side in ['head']:")
runner=runner.replace('complete base/head25 runs start.','one fresh full25 HEAD starts; BASE is adopted.')
(OUT/'run-head.py').write_text(runner)
for name in ['index-sources.py','analyze-screens.py']:(OUT/name).write_bytes((OLD/name).read_bytes())
hardness=next(r for r in capture['sides']['head']['files'] if r['path'].endswith('/Hardness.lean'))
assert hardness['sha256'].startswith('3c41a6ac')
print(json.dumps(dict(prepared=str(OUT),base=base,head=head,campaign=campaign,population=25,
    source_lines={side:sum(r['lines'] for r in capture['sides'][side]['files']) for side in ['base','head']},
    hardness_sha256=hardness['sha256'],baseline_adopted=True,head_not_yet_run=True),indent=2))
