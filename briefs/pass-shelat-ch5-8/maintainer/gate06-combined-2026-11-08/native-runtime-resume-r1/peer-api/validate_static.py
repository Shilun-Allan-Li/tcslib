"""Own read-only AST/data validation; never import or execute reviewed programs."""
from pathlib import Path
import ast
import hashlib
import json
import re

W = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
A = W / '.lake/ps-maintainer/gate06-combined-20261108'
P = A / 'native-runtime-resume-r1'
OUT = P / 'peer-api'
HEAD = 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
PINS = {
    'continue_native.py': '921959c0d81c4ffb7e2cedd38e540be69e19e8d62ec8f3743b7bd0ad6117369c',
    'R1-FINGERPRINTS.json': '47c3740c7e5abaf68fe9a82cdb0eba405ea9acdf51a7c14248a16b5817e7beaa',
    'PROPOSAL-MANIFEST.json': '2de8a659bf2c4f3e7306d09132272111fe69d497d3aef73c266529558e35ddaa',
    'README.md': 'e6f69e8bc0700f7b51981d824ab749d70e4d0ee14bb92d19bfd1155b15d56f5e',
    'validation.json': '37d91cb937a7da27461e1df3e22495e9305f03bccd8e6e38af6d9a33e00f464b',
}
ENGINE = A / 'native-runtime-proposal/run_combined_native.py'
ENGINE_SHA = '64b5b2ff2260a48eef55dcf77bdb5c4125459170b28c30499f60a93de7da3c95'
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def need(value, label):
    if not value: raise AssertionError(label)
def main():
    for name, expected in PINS.items(): need(digest(P/name) == expected, name+' pin')
    need(digest(ENGINE) == ENGINE_SHA, 'engine pin')
    tree = ast.parse((P/'continue_native.py').read_text())
    engine_tree = ast.parse(ENGINE.read_text())
    manifest = load(P/'PROPOSAL-MANIFEST.json')
    need(manifest['head'] == HEAD, 'proposal head')
    for row in manifest['files']:
        f=P/row['path']; need(f.stat().st_size == row['bytes'] and digest(f) == row['sha256'], 'proposal leaf')
    # Structural checks supplement the human full-source read, not semantics execution.
    calls = [ast.unparse(n.func) for n in ast.walk(tree) if isinstance(n,ast.Call)]
    need(not any(x.startswith('subprocess.') or x in {'os.kill','os.killpg'} for x in calls), 'no new native launch/signal')
    need(calls.count('E.Run.check') == 1, 'one engine delegation site')
    needs = [n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name == 'main']
    need(len(needs)==1 and any(isinstance(n,ast.Call) and ast.unparse(n.func)=='spec.loader.exec_module' for n in ast.walk(needs[0])), 'engine import is in main')
    need(sum(1 for n in ast.walk(tree) if isinstance(n,ast.Call) and ast.unparse(n.func)=='spec.loader.exec_module') == 1, 'single pinned import')
    ast.parse((OUT/'validate_static.py').read_text())
    R=A/'native-bootstrap-r1'; inventory=load(P/'R1-FINGERPRINTS.json')
    need(inventory['source_head']==HEAD and Path(inventory['root'])==R, 'R1 provenance')
    need(len(inventory['files'])==len({r['path'] for r in inventory['files']})==21, '21 unique raw files')
    need({str(f.relative_to(R)) for f in R.rglob('*') if f.is_file()} == {r['path'] for r in inventory['files']}, 'R1 exact file set')
    for row in inventory['files']:
        f=R/row['path']; need(f.stat().st_size==row['bytes'] and digest(f)==row['sha256'], 'R1 raw bytes')
    need(not (R/'RESULT.json').exists(), 'failed R1 no aggregate')
    rows=[json.loads(x) for x in (R/'attempts.jsonl').read_text().splitlines()]
    need(len(rows)==3, 'three R1 attempts')
    ext=load(R/'external-before.json')
    pfr=load(A/'native-prep/external-r1/pfr-modules.json')
    need(len(pfr)==len({r['module'] for r in pfr})==31, '31 PFR identities')
    need(rows[0]['label']=='CacheProbe' and [r['module'] for r in rows[1:]] == ['.lake/packages/PFR/'+r['package_relative_source'][:-5] for r in pfr[:2]], 'exact R1 sequence')
    ordinary=None
    compact=[]
    for index,row in enumerate(rows):
        d=Path(row['log']).parent
        start=load(d/'start.json'); child=load(d/'child.json'); text=(d/'native.log').read_text()
        need(load(d/'end.json')==row and digest(d/'native.log')==row['log_sha256'], 'end/log receipt')
        need(json.loads(text.splitlines()[0])==start, 'raw start header')
        need(json.loads(text.splitlines()[-1])=={'event':'END','utc':row['end_utc'],'rc':row['rc'],'interrupted':row['interrupted']}, 'raw END footer')
        need(row['head']==start['head']==HEAD and start['source_sha256']==row['source_sha256'], 'head/source metadata')
        need(row['source_sha256']==row['source_sha256_before']==row['source_sha256_after']==digest(W/(row['module']+'.lean')) and row['source_unchanged'], 'current R1 source pin')
        need(row['dependencies_before']==row['dependencies_after']==start['dependencies_before'], 'receipt prerequisite stability')
        need(not row['dependencies_before']['local'], 'R1 local imports absent')
        for name,dep in row['dependencies_before']['external'].items():
            expected=ext[name]
            need(all(dep[k]==v for k,v in expected.items()), 'R1 external snapshot row')
        need(child['pgid']==child['pid'] and child['runner_pid']>0 and child['command']==['/usr/bin/time','-l','bash','scripts/lean_check_tree.sh',row['module']], 'child identity/command')
        need(row['runner_sha256']==row['runner_sha256_after']==start['runner_sha256']==ENGINE_SHA, 'R1 engine identity')
        need(row['error_diagnostics']==len(re.findall(r'\berror(?:\([^)]*\))?:',text))==0, 'zero diagnostics')
        obj=A/'oleans-r1'/(row['module']+'.olean')
        if index<2:
            need(row['passed'] is True and row['rc']==0 and row['interrupted'] is None and row['post_validation_error'] is None and row['fresh_nonempty_object'], 'R1 success')
            need(obj.is_file() and obj.stat().st_size>0 and digest(obj)==row['object_sha256'], 'two current successful objects')
            rss=re.search(r'^\s*(\d+)\s+maximum resident set size\s*$',text,re.M)
            need(rss is not None and int(rss[1])==row['max_rss_bytes_macos'], 'success RSS')
            if index==0:
                need(text.splitlines().count('G06-COMBINED-CACHE-383 EOF')==1, 'cache marker')
                ordinary=start['PATH']
            else:
                need(start['PATH']==str(A/'pfr-runtime-r1/bin')+':'+ordinary and start['pfr_only_PATH'] is True, 'PFR only path')
                ext[pfr[0]['module']]={'object_path':str(A/'oleans-r1'/(pfr[0]['module'].replace('.','/')+'.olean')),'object_sha256':row['object_sha256'],'object_bytes':obj.stat().st_size,'source_sha256':row['source_sha256'],'kind':'PFR_OWN_TREE'}
        else:
            need(row['passed'] is False and row['rc']==-15 and row['object_sha256'] is None and not row['fresh_nonempty_object'] and not obj.exists(), 'failed Kernel object absent')
            node=ast.parse(row['interrupted'],mode='eval').body
            need(isinstance(node,ast.Call) and ast.unparse(node.func)=='RuntimeError' and len(node.args)==1 and not node.keywords, 'exact RuntimeError shape')
            message=ast.literal_eval(node.args[0]); prefix='HOST_COLLISION: another native operation started: '
            need(message.startswith(prefix), 'exact host reason')
            foreign=json.loads(message[len(prefix):])
            need(foreign and all(r['pgid'] != child['pgid'] for r in foreign) and row['post_validation_error']=="RuntimeError('Native checker failed')", 'isolated host failure')
        compact.append({k:row[k] for k in ['label','module','rc','passed','object_sha256','interrupted']})
    order=(A/'native-prep/plan-r1/rebuild-order.txt').read_text().splitlines()
    modules=load(A/'native-prep/plan-r1/modules.json'); copy=load(A/'native-prep/plan-r1/copy-plan.json')
    positions={r['module']:i for i,r in enumerate(modules)}
    need(len(modules)==len(positions)==1075 and len(order)==len(set(order))==638 and len(copy)==437, 'scope counts')
    need(set(order).isdisjoint({r['module'] for r in copy}) and set(order)|{r['module'] for r in copy}==set(positions), 'exact partition')
    need(all(positions[d]<positions[r['module']] for r in modules for d in r['local_imports']), 'topological dependency order')
    need({'TCSlib','audits/pass-shelat/Checks'}<=set(order), 'root and Checks fresh local')
    need(all(not r['module'].startswith('PFR.') or all(not d.startswith('PFR.') or next(i for i,x in enumerate(pfr) if x['module']==d)<j for d in r['imports']) for j,r in enumerate(pfr)), 'PFR topological order')
    data={'status':'STATIC_AST_AND_RAW_DATA_VALIDATION_PASS_NO_PROGRAM_EXECUTION','head':HEAD,'pins':PINS,'engine_sha256':ENGINE_SHA,'R1_raw_files_verified':21,'R1_attempts':compact,'required_bootstrap_successes':36,'R1_reused_successes':2,'R1_retained_failures':1,'minimum_new_bootstrap_native_calls':34,'minimum_total_history_native_attempts_bootstrap':37,'required_fresh_local_successes':638,'minimum_total_history_native_attempts_final':675,'warm_objects':437,'final_local_objects':1075,'limits':['No coordinator or engine import/execution; no native/process simulation.','Full 146 historical and 3810 external object rehashes are runtime guards, not independently executed by this static review.','Current objects for the two R1 successful native attempts alone were independently hashed.']}
    with (OUT/'validation.json').open('x') as f: json.dump(data,f,indent=2); f.write('\n')
    print(json.dumps({'status':data['status'],'validation_sha256':digest(OUT/'validation.json')}))
if __name__=='__main__': main()
