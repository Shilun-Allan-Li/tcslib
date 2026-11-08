"""Verify and freeze the fresh79 HEAD against its adopted actual25 BASE."""
from pathlib import Path
import base64, datetime, hashlib, io, json, subprocess, tarfile
ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final79'
OLD=OUT.parent/'round3-current-source-screen25-final'
ORIGINAL=OUT.parent/'round3-current-source-screen25'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
(OUT/'freeze79.py').write_bytes(Path(__file__).read_bytes())
c=json.loads((OUT/'capture.json').read_text());delta=json.loads((OUT/'pair-delta.json').read_text())
assert len(c['population'])==25 and c['head']=='79e7c63a6bfa5f002663924f5c7d4e72db705026'
assert sha((OLD/'SHA256SUMS').read_bytes())=='43b179e6b7abc5cca8cbca07c93e05f8a5d543d24627f521c2d20a3b1cd4f4ec'
for folder in [OLD,ORIGINAL]:
    for line in (folder/'SHA256SUMS').read_text().splitlines():
        digest,path=line.split('  ',1);assert sha((folder/path).read_bytes())==digest
indexes={};pairs={}
for side in ['base','head']:
    assert git('rev-parse',c[side]+'^{commit}').decode().strip()==c[side]
    assert git('cat-file','-t',c[side]).strip()==b'commit'
    arc=base64.b64decode((OUT/(side+'.tar.base64.txt')).read_bytes())
    assert sha(arc)==c['sides'][side]['archive_sha256']
    with tarfile.open(fileobj=io.BytesIO(arc)) as tar:
        assert {m.name for m in tar.getmembers() if m.isfile()}==set(c['population'])
        for row in c['sides'][side]['files']:
            b=(OUT/'inputs'/side/(row['path']+'.txt')).read_bytes()
            assert b==tar.extractfile(row['path']).read()==git('show',c[side]+':'+row['path'])
            assert sha(b)==row['sha256'] and len(b)==row['bytes']
            assert git('rev-parse',c[side]+':'+row['path']).decode().strip()==row['blob']
            assert (Path(c['temporary_trees'][side])/row['path']).read_bytes()==b
    run=json.loads((OUT/(side+'-run.json')).read_text());raw=(OUT/(side+'.out')).read_bytes()
    assert run['exit']==0 and run['output_sha256']==sha(raw) and run['bytes']==len(raw)
    assert run['full_population']==25 and run['command'][7:]==list(c['population'])
    indexes[side]={r['label']:r for r in json.loads((OUT/(side+'-index.json')).read_text())}
    pairs[side]=json.loads((OUT/(side+'-candidates.json')).read_text())
    assert len(pairs[side])==delta[side]['candidates'] and len(indexes[side])==delta[side]['declarations']
    assert sum(r['shared'] for r in pairs[side])==delta[side]['reproduced_chars']
    assert len({(r['a'],r['b']) for r in pairs[side]})==len(pairs[side])
    assert all(r['denominator']==indexes[side][r['b']]['body_chars'] for r in pairs[side])
assert (OUT/'base.out').read_bytes()==(ORIGINAL/'base.out').read_bytes()
assert (OUT/'base-run.json').read_bytes()==(ORIGINAL/'base-run.json').read_bytes()
assert (OUT/'population.txt').read_bytes()==(ORIGINAL/'population.txt').read_bytes()
tool='scripts/copy-text-screen-v3.py';tb=(ROOT/tool).read_bytes()
assert sha(tb)==c['tools'][tool]=='f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181'
assert tb==(OUT/'tools/copy-text-screen-v3.py.txt').read_bytes()==git('show',c['head']+':'+tool)
events=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
assert [e['event'] for e in events]==['waiting','acquired','released']
run=json.loads((OUT/'head-run.json').read_text());assert run['orchestrator_sha256']==sha((OUT/'run-head.py').read_bytes())
assert events[1]['utc']<=run['start_utc']<=run['end_utc']<=events[2]['utc']
schedule=json.loads((OUT/'scheduling-check-head.json').read_text());assert int(schedule['actual_process_snapshot'].split()[1])==10
terms={side:{k:r for k,r in rows.items() if r['kind']=='term'} for side,rows in indexes.items()}
assert terms['base'].keys()==terms['head'].keys() and len(terms['base'])==435
assert all(terms['base'][k]['normalized_body']==terms['head'][k]['normalized_body'] for k in terms['base'])
assert [r for r in pairs['base'] if r['kind']=='term']==[r for r in pairs['head'] if r['kind']=='term']

def k(change,row):
    r=row['head'] if change=='changed' else row
    return change,r['a'],r['b']
actual={k(change,r):r for change,rs in [('new',delta['new']),('gone',delta['gone']),('changed',delta['changed_measurements'])] for r in rs}
classes=[]
for row in json.loads((OLD/'head-delta-classification.json').read_text())['rows']:
    key=k(row['change'],row['row']);assert actual[key]==row['row'];classes.append(row)
extra=[(key,row) for key,row in actual.items() if key not in {k(r['change'],r['row']) for r in classes}]
assert len(extra)==4
for key,row in extra:
    assert key[0]=='gone' and row['a']=='Tautology.lean::taut_comp_on_image'
    classes.append(dict(change='gone',row=row,group='RIMAGE: shared raw on-image contract citation',assessment='One private raw image-composition implementation is replaced by its already imported public theorem, with exact name/header/budget preserved. These four lost directed spans are one implementation re-point, not four retired declarations. The private citation survives below the60-character screen threshold; retirement on campaign occurs only on merge.'))
assert {k(r['change'],r['row']) for r in classes}==set(actual)
save('head-delta-classification.json',dict(scope='Every actual final79/base directed delta; prior31 source-identical dispositions retained after exact measurement checks, plus four image-repair removals. No global debt/gate clearance.',rows=classes))
oldpairs=json.loads((OLD/'head-candidates.json').read_text());oldmap={(r['a'],r['b']):r for r in oldpairs};newmap={(r['a'],r['b']):r for r in pairs['head']}
assert not(newmap.keys()-oldmap.keys())
gone=[oldmap[key] for key in sorted(oldmap.keys()-newmap.keys())]
assert len(gone)==4 and all(r['a']=='Tautology.lean::taut_comp_on_image' for r in gone)
assert all(oldmap[key]==newmap[key] for key in newmap)
save('previous63-to-final79-delta.json',dict(previous=c['previous_head'],head=c['head'],new=[],gone=gone,changed_measurements=[],scope='Complete independently executed HEAD outputs compared; no old result substitutes for final tiling.'))
pairtool=ROOT/'devtools/seyoon/pairdiff.py';pb=pairtool.read_bytes();(OUT/'tools/pairdiff.py.txt').write_bytes(pb)
requests=[]
for label,earlier in [('base',OUT/'base.out'),('previous63',OLD/'head.out')]:
    command=['python3','-I',str(pairtool),str(OUT/'head.out'),str(earlier)];q=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    (OUT/('canonical-pairdiff-'+label+'.out')).write_bytes(q.stdout);(OUT/('canonical-pairdiff-'+label+'.stderr.out')).write_bytes(q.stderr)
    assert q.returncode==0
    requests.append(dict(comparison=label,command=command,exit=q.returncode,tool_sha256=sha(pb),stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr)))
save('canonical-pairdiff-runs.json',requests)
lint=json.loads((OUT/'lint-results.json').read_text());assert all(not r['normalized_new'] for r in lint['delta'].values())
assert json.loads((OUT/'source-freeze-complete-headers.json').read_text())['all25_common_headers_public_names_visibility_preserved']
assert json.loads((OUT/'source-term-attribute-freeze.json').read_text())['all25_source_terms_attributes_identical']
image=json.loads((OUT/'on-image-sweep-final.json').read_text());assert image['exact_raw_contract_members']==2 and image['new_raw_rederivations_eligible_for_mechanical_repoint']==0
assert len(classes)==len(delta['new'])+len(delta['gone'])+len(delta['changed_measurements'])
save('verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),base=c['base'],head=c['head'],source_inputs_verified=50,
    baseline_mode='Actual executed BASE875.403s adopted; no BASE tiling rerun',fresh_head_exit=0,head_seconds=run['seconds'],lock_released=True,niceness_observed=10,
    all_raw_candidates_accounted=True,all_delta_rows_classified=len(classes),all435_eligible_terms_identical=True,
    all25_complete_headers_terms_attributes_preserved=True,source_raw_image_members=2,raw_image_reconstructions_found=0,
    lints_no_new_diagnostics=True,no_Lean_source_Git_cache_mutation_by_task=True,no_gate_debt_or_merge_approval=True))

readme=f'''# Final79 source/copy-text evidence

**Not yet clear to merge: #215 (gate closure and current replay are separate parent-owned requirements).**

Fresh full25 HEAD at `{c['head']}` passed and released the shared screen lock.
The identical actual BASE at `{c['base']}` is adopted after exact source/tool/population/
archive/raw-receipt checks. No BASE tiling was repeated. This source evidence claims no
Lean elaboration, seal, axiom check, replay, global duplication clearance or gate closure.

| Measure | Adopted BASE | Fresh79 HEAD |
|---|---:|---:|
| Eligible canonical source spans | {delta['base']['declarations']:,} | {delta['head']['declarations']:,} |
| Directed candidates | {delta['base']['candidates']:,} | {delta['head']['candidates']:,} |
| Canonical reproduced characters | {delta['base']['reproduced_chars']:,} | {delta['head']['reproduced_chars']:,} |

HEAD actually ran {run['seconds']:.3f}seconds, {run['start_utc']}–{run['end_utc']},
nice10/Python-I, under its own shared-lock acquisition. Original BASE timestamps/command/
exit remain verbatim in its adoption receipt. Full25 inputs on both sides, exact blobs,
archives, actual exports, tool/runner hashes, raw outputs/complete indexes and all candidates
are retained without caps. This is the same named25-source union, not recursive import
closure; neither new import nor this proof fix requires a26th source.

BASE→79 has {len(delta['new'])}new, {len(delta['gone'])}gone and {len(delta['changed_measurements'])}changed retained
scores; all{len(classes)} rows are dispositioned. Canonical pairdiff output is retained
against BASE and historical63. From63→79 exactly four directed rows disappear and every
other row/score is identical. They arise from ONE raw image-composition implementation,
now a short public citation. It is not four deleted declarations. Its private name, exact
header and2*T1+T2+2 budget remain. Implementation debt retires on merge, not this check.

The two new BASE-relative rows remain: shared lenLe application/refolding89/167 in the
unary-comparison wrapper, and the already reviewed SingleTape growth-phase784/1564 row.
Sixteen earlier removals and thirteen changed adapter/phase scores remain fully visible,
including127→525shared guard text and279→176map-wrapper text. All259 term candidate rows
and all435 eligible term spans are identical BASE/HEAD; no executable source change occurs.

Complete header checks handle nested input defaults AND top-level let initializers in
result types. All25 common public/private headers and visibility are preserved; three
old private Segment concatenators are replaced by three bridges. Full source term chunks
and attribute lines are unchanged. These are source parser facts, not compiler/notation
or elaborated-type census claims. The standard screen itself is unmodified: some legacy
spans contain result-type suffixes or following scope commands. Raw denominators are not
adjusted or mislabeled as necessarily pure proof characters.

Fresh canonical HEAD CLI lints against adopted actual BASE CLI outputs: style153→153;
campaign/check8b0FAIL/28WARN/28INFO→same; no normalized new diagnostic. Style's actual
exit1 reflects inherited findings; campaign exits0. Full stdout/stderr/requests retained.
Old size/doc/sketch findings are not waived. One generator-pattern assertion was corrected
before its target script was created; generator-attempt1.json preserves it. No screen failed.

The bounded five-touched-file raw on-image sweep retains all15 candidates and inline
closings. Both exact raw-contract members—SAT and Tautology—now cite the SAME existing
public `Turing.FinTM.exists_comp_on_image`. No reconstructing raw member remains under
the complete-signature/operational-hook sweep. Hardness.clNative_image is different
class-level partial-image polynomial packaging, not automatically the total FP.comp
contract, a confirmed new API necessity or a newly acknowledged family. Its seven clients
are not counted as seven separate raw composition recipes.

Seven Gate106 retention kinds remain exact and temporary: clean/lifting, positive-release
stop, K-tape padding, finite one-way transducer, polynomial bridge overhead, finite-family
shared-bank dispatcher, and existing unary-clock clean-call host/actual-orbit wrappers.
Owner is maintainer; window next12.2c after activeMIG1 and before further SAT/Hardness fills.
Named retained lower bounds SAT34/270 and Hardness49/544 are not exhaustive duplicate
censuses; do not subtract the separate closure repairs from that retained union. On-image
class packaging is outside these rulings. The separately recorded FE-LIVE-1 acknowledgment
covers existing FIXED LIVE-stop first-entry counterparts; it is not an eighth Gate106 kind
or a None-halt/nonabsorbing/future-copy extension. Exact ruling limits are retained.

The expanded baseline still exposes material old Catalog/Loop and canonical id/const
definition/proof correspondences. Broader source/kind buckets are not all declared accepted,
harmless client data or different T5 tables. Historical complete23-bucket baseline
classification remains available in preceding generations, with canonical-span limits and
current seven-kind/FE-LIVE context explicit here. No global semantic exhaustion or one-fifth
clearance follows from this bounded review. No source/API/Git/cache/snapshot change,
commit/push, Lean execution or external dispatch was performed. SHA256SUMS freezes all
other retained files; parent owns replay/gate/ledger/publication disposition.
'''
(OUT/'README.md').write_text(readme)
assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))
manifest=[]
for path in sorted(OUT.rglob('*')):
    if path.is_file() and path.name!='SHA256SUMS':manifest.append(sha(path.read_bytes())+'  '+str(path.relative_to(OUT)))
(OUT/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
for line in manifest:
    digest,path=line.split('  ',1);assert sha((OUT/path).read_bytes())==digest
print(json.dumps(dict(frozen_files=len(manifest),manifest_sha256=sha((OUT/'SHA256SUMS').read_bytes()),readme_sha256=sha((OUT/'README.md').read_bytes()),head_pairs=delta['head']['candidates']),indent=2))
