from pathlib import Path
import os,json,subprocess,hashlib,datetime,re
r=Path.cwd();s=Path(os.environ['TCSLIB_SCRATCH']);wt=s/'wt-epad';out=Path(__file__).resolve().parent;start=json.loads((out.parent/'replay-mmig1-start.json').read_text())
def pin(ref):
 h=subprocess.check_output(['git','-C',str(wt),'rev-parse',ref],text=True).strip();subprocess.run(['git','-C',str(wt),'cat-file','-e',h+'^{commit}'],check=True);return h
head=pin('HEAD');assert head==start['head'];assert not subprocess.check_output(['git','-C',str(wt),'status','--porcelain','--untracked-files=no'])
for name in ['replay-mmig1.sh','precheck-mmig1.sh','down-mmig1.txt','replay-mmig1.log','replay-mmig1-static.txt']:
 (out/name).write_bytes((s/'fills/replay'/name).read_bytes())
log=(out/'replay-mmig1.log').read_text();static=(out/'replay-mmig1-static.txt').read_text();rows=re.findall(r'^(TCSlib[^ \n]*) exit=(\d+) errors=(\d+) sorry=(\d+)$',log,re.M)
assert len(rows)==394 and len({x[0] for x in rows})==394 and all(x[1]=='0' and x[2]=='0' for x in rows)
assert log.splitlines()[-1]=='# modules=394 failed=0' and static.splitlines()[-1]=='modules 394, mismatches 0, static total 60'
assert [x[0] for x in rows]==(out/'down-mmig1.txt').read_text().splitlines()
assert sum(int(x[3]) for x in rows)==60
current=pin('origin/complexity/arora-barak-ch3-4');assert not subprocess.check_output(['git','-C',str(wt),'diff','--name-only',start['snapshot_tree'],current,'--','*.lean'])
receipt={'completed_receipt_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'PR':233,'head':head,'campaign_at_start':start['campaign'],'campaign_at_receipt':current,'campaign_Lean_unchanged_from_snapshot':True,'snapshot_parent':'oleans-mac3','result_complete_tree':'oleans-mmig1','modules':394,'failures':0,'static_mismatches':0,'static_total':60,'executed_pipeline_exit':0,'source_tracked_clean_at_receipt':True,'downstream_scope':'Full generated downstream closure of all11 changed Lean modules; no root TCSlib module. Separate producer641-module sweep is not this394-module replay.','subsequent_proof_proposals_not_applied':True,'artifact_sha256':{name:hashlib.sha256((out/name).read_bytes()).hexdigest() for name in ['replay-mmig1.sh','precheck-mmig1.sh','down-mmig1.txt','replay-mmig1.log','replay-mmig1-static.txt']}}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
(out/'STATUS.md').write_text('''# Passed draft merged-tree replay

**PASS394/0, static0 mismatches/60 total.** The prescribed mmig1 pipeline completed with
exit0 at draft source head `0d6b6f842a48be813dcde7fdfd2a1a161fab2383`. It compiled the entire
generated394-module downstream closure of the eleven changed modules from a whole copy
of current campaign snapshot mac3. Root TCSlib is excluded as required. The producer's
separate641-module sweep is not claimed as this native replay.

`receipt.json` checks every module row, module order, static total, clean exact source pin
and unchanged campaign Lean. Complete script/precheck/order/log/static outputs are retained.
The resulting complete `oleans-mmig1` tree is preserved. Later screen-driven proposals are
not applied in this generation and do not retroactively change these source hashes.
Interface rulings and external gate118 remain open; this pass alone is not merge clearance.
''')
(out/'receipt-assembly-notes.md').write_text('The first offline receipt assembly incorrectly converted the log module paths to dots while the retained order uses slashes. Its equality assertion aborted before writing a success receipt. Direct comparison of all394 exact slash paths passes; the native replay and static outputs are unchanged.\n')
files=sorted(f for f in out.iterdir() if f.is_file() and f.name!='SHA256SUMS');(out/'SHA256SUMS').write_text(''.join(hashlib.sha256(f.read_bytes()).hexdigest()+'  '+f.name+'\n' for f in files))
print('Archived exact394-module PASS, static60/0 mismatches; source frozen, proposed followups not applied.')
