"""Capture both fresh full23 F6 source trees; no tiling or Lean execution."""
from pathlib import Path
import base64, datetime, hashlib, io, json, os, subprocess, tarfile, tempfile
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/fills/f6/landing/source-screen23'
POP=ROOT/'campaign/fills/f6/issue-preparation/inputs/screen-population.txt'
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def pin(ref):
    x=git('rev-parse',ref+'^{commit}').decode().strip();assert git('cat-file','-t',x).strip()==b'commit';return x
base=pin('3023dc1408c3d216fc07a7cbba9ae30135b861ed');head=pin('f72a807e2376a2b986675c992745d6affc23b96f')
population=POP.read_text().splitlines();assert len(population)==len(set(population))==21
added=['TCSlib/Complexity/SpaceComplexity/Inclusions.lean','TCSlib/Complexity/SpaceComplexity/ConfigCount.lean']
assert not set(added)&set(population);population+=added
assert len(population)==23 and len(set(population))==23
changed=git('diff','--name-only',base,head,'--','*.lean').decode().splitlines()
owner='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean';assert changed==[owner]
OUT.mkdir(exist_ok=False);(OUT/'prepare.py').write_bytes(Path(__file__).read_bytes())
scratch=Path(tempfile.mkdtemp(prefix='tcslib-f6-screen23-',dir='/private/tmp'))
capture=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=base,head=head,population=population,
    issued21=str(POP.relative_to(ROOT)),issued21_sha256=sha(POP.read_bytes()),added_complete_sources=added,changed_files=changed,temporary_trees={},sides={},tools={})
for side,commit in [('base',base),('head',head)]:
    archive=git('archive','--format=tar',commit,'--',*population)
    (OUT/(side+'.tar.base64.txt')).write_bytes(base64.encodebytes(archive));tree=scratch/side;tree.mkdir();rows=[]
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        members=[m for m in tar.getmembers() if m.isfile()];assert {m.name for m in members}==set(population)
        for member in members:
            path=member.name;b=tar.extractfile(member).read();blob=git('rev-parse',commit+':'+path).decode().strip()
            assert b==git('cat-file','blob',blob)
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
            inert=OUT/'inputs'/side/(path+'.txt');inert.parent.mkdir(parents=True,exist_ok=True);inert.write_bytes(b)
            target=tree/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b)
            rows.append(dict(path=path,blob=blob,sha256=sha(b),bytes=len(b),lines=len(b.splitlines())))
    capture['temporary_trees'][side]=str(tree);capture['sides'][side]=dict(archive_sha256=sha(archive),archive_bytes=len(archive),files=rows)
tool='scripts/copy-text-screen-v3.py';code=(ROOT/tool).read_bytes()
assert sha(code)=='f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181'
assert code==git('show',base+':'+tool)==git('show',head+':'+tool)
capture['tools'][tool]=sha(code);(OUT/'tools').mkdir();(OUT/'tools/copy-text-screen-v3.py.txt').write_bytes(code)
headrow=next(r for r in capture['sides']['head']['files'] if r['path']==owner)
assert headrow['sha256']=='8a44b4b35010ac116e34880269b80d1121d2fdd86166e62da75efeffc984c031'
wt=Path('/Users/seyoonr/.codex/worktrees/ab34-natbits/tcslib-arora-barak-ch3-4')
wt_head=subprocess.run(['git','-C',str(wt),'rev-parse','HEAD'],check=True,stdout=subprocess.PIPE).stdout.decode().strip()
assert wt_head==head and subprocess.run(['git','-C',str(wt),'diff','--name-only','HEAD','--','*.lean'],check=True,stdout=subprocess.PIPE).stdout==b''
capture['actual_worktree']=str(wt);capture['actual_worktree_head']=wt_head
(OUT/'capture.json').write_text(json.dumps(capture,indent=2)+'\n')
(OUT/'population.txt').write_text('\n'.join(population)+'\n');(OUT/'issued21-population.txt').write_bytes(POP.read_bytes())
(OUT/'changed-files.txt').write_text(owner+'\n')
(OUT/'source.diff').write_bytes(git('diff','--no-ext-diff','--no-color',base,head,'--','*.lean'))
OLD=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25'
runner=(OLD/'run-screens.py').read_text()
assert runner.count('ROOT = OUT.parents[4]')==1;runner=runner.replace('ROOT = OUT.parents[4]','ROOT = OUT.parents[4]')
# fills/f6/landing/source-screen23 and gates106/review/folder have the same depth.
assert OUT.parents[4]==ROOT
assert runner.count('complete base/head25 runs start.')==1;runner=runner.replace('complete base/head25 runs start.','complete fresh F6 base/head23 runs start.')
(OUT/'run-screens.py').write_text(runner)
for name in ['index-sources.py','analyze-screens.py']:(OUT/name).write_bytes((OLD/name).read_bytes())
(OUT/'POPULATION.md').write_text('''# F6 full23 source population

Both BASE and HEAD are freshly screened over the exact issued21 full source files plus
SpaceComplexity/Inclusions and SpaceComplexity/ConfigCount. Neither additional home was
already present under an alias. Inclusions is an actual identity-comparison citation;
ConfigCount supplies the published visited-set monotonicity fact used by the final fix.
The original21-file metrics remain separately attributed history and are not a baseline
substitute. No population cap, source subset, output splice or global recursive import-
closure claim. All46 source blobs, archives and temporary exports are retained/verified.
''')
print(json.dumps(dict(base=base,head=head,population=23,head_source_sha256=headrow['sha256'],source_lines={s:sum(r['lines'] for r in capture['sides'][s]['files']) for s in ['base','head']},temporary_trees=capture['temporary_trees'],no_screen_yet=True),indent=2))
