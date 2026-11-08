"""Freeze the actually executed63 generation, now explicitly historical."""
from pathlib import Path
import base64, datetime, hashlib, io, json, subprocess, tarfile, sys

ROOT=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
OUT=ROOT/'campaign/gates/106-sg1-dedup/review/round3-current-source-screen25-final'
OLD=OUT.parent/'round3-current-source-screen25'
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(OUT/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
(OUT/'freeze63.py').write_bytes(Path(__file__).read_bytes())
c=json.loads((OUT/'capture.json').read_text());d=json.loads((OUT/'pair-delta.json').read_text())
assert c['head']=='63a3ce018e96c8c114b9c82f8d5fce6021c7d03c' and len(c['population'])==25
successor=git('rev-parse','79e7c63a6bfa5f002663924f5c7d4e72db705026^{commit}').decode().strip()
assert git('cat-file','-t',successor).strip()==b'commit'
for side in ['base','head']:
    assert git('rev-parse',c[side]+'^{commit}').decode().strip()==c[side]
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
    assert run['exit']==0 and run['output_sha256']==sha(raw) and run['full_population']==25
    assert run['command'][7:]==list(c['population'])
    rows=json.loads((OUT/(side+'-candidates.json')).read_text());ix={r['label']:r for r in json.loads((OUT/(side+'-index.json')).read_text())}
    assert len(rows)==d[side]['candidates'] and sum(r['shared'] for r in rows)==d[side]['reproduced_chars']
    assert len({(r['a'],r['b']) for r in rows})==len(rows)
    assert all(r['denominator']==ix[r['b']]['body_chars'] for r in rows)
assert (OUT/'base.out').read_bytes()==(OLD/'base.out').read_bytes()
assert (OUT/'base-run.json').read_bytes()==(OLD/'base-run.json').read_bytes()
assert (OUT/'head.out').read_bytes()==(OLD/'head.out').read_bytes()
assert d==json.loads((OLD/'pair-delta.json').read_text())
classes=json.loads((OLD/'head-delta-classification.json').read_text())
classes['scope']='All31 actual63/adoptedBASE delta rows exactly equal historical d0 measurements. Dispositions reused after exact raw-output/source-context checks, not a substituted HEAD run. Separate newly confirmed raw-image repair remains required at63.'
save('head-delta-classification.json',classes)
pairtool=ROOT/'devtools/seyoon/pairdiff.py';toolbytes=pairtool.read_bytes();(OUT/'tools/pairdiff.py.txt').write_bytes(toolbytes)
command=['python3','-I',str(pairtool),str(OUT/'head.out'),str(OUT/'base.out')]
q=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
(OUT/'canonical-pairdiff.out').write_bytes(q.stdout);(OUT/'canonical-pairdiff.stderr.out').write_bytes(q.stderr)
assert q.returncode==0 and q.stdout.decode().splitlines()[0]=='head pairs 1999; union of earlier 2013; new at head 2; earlier-only 16'
save('canonical-pairdiff-run.json',dict(command=command,exit=q.returncode,tool_sha256=sha(toolbytes),stdout_sha256=sha(q.stdout),stderr_sha256=sha(q.stderr)))
events=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
assert [r['event'] for r in events]==['waiting','acquired','released']
run=json.loads((OUT/'head-run.json').read_text());assert run['orchestrator_sha256']==sha((OUT/'run-head.py').read_bytes())
schedule=json.loads((OUT/'scheduling-check-head.json').read_text());assert int(schedule['actual_process_snapshot'].split()[1])==10
lint=json.loads((OUT/'lint-results.json').read_text())
assert all(not row['normalized_new'] and not row['normalized_gone'] for row in lint['delta'].values())
assert json.loads((OUT/'source-freeze-complete-headers.json').read_text())['all25_common_headers_public_names_visibility_preserved']
assert json.loads((OUT/'on-image-sweep-final.json').read_text())['new_raw_rederivations_eligible_for_mechanical_repoint']==1
save('verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='HISTORICAL63, successor79 requires its own fresh HEAD screen',
    base_mode='Actual prior BASE adopted by exact sources/tool/population/raw receipt; no repeated BASE tiling',
    fresh_head_executed=True,head_exit=0,head_seconds=run['seconds'],lock_released=True,
    head_output_identical_to_previous_d0=True,source_inputs_verified=50,all31_delta_dispositions_retained=True,
    all25_complete_headers_preserved=True,lints_style=[153,153],lints_campaign_fail=[0,0],lints_campaign_warn=[28,28],
    source_only_image_sweep='Two exact raw contracts; SAT already cites public API; Taut reconstructs, parent assigned repair. Class-level Hardness wrapper separate.',
    successor=successor,no_Lean_source_Git_cache_mutation_by_task=True,no_gate_or_debt_approval=True))
readme='''# Historical63 source-screen generation

**Not yet clear to merge: #215 (this is the pre-Tautology-fix generation; final-source gate/replay remain pending).**

Fresh full25 HEAD screening at `63a3ce018e96c8c114b9c82f8d5fce6021c7d03c` passed.
Its exact output equals the earlier d0 HEAD output, despite the newly approved weighted-bound
reader/import repair. The run was actually executed for1,124.364seconds, at observed nice10,
2026-11-08 00:38:46–00:57:31UTC. The shared lock was released. It is now historical:
the parent committed the additional mechanical Tautology citation fix at
`79e7c63a6bfa5f002663924f5c7d4e72db705026`, whose fresh HEAD check is separate.

BASE is the ACTUALLY EXECUTED full25 run at `3023dc1408c3d216fc07a7cbba9ae30135b861ed`
from the prior frozen folder (875.403seconds). All101 prior manifest entries, population,
tool bytes,25 BASE blobs/archive and the raw execution receipt were checked. Current
campaign `8eb2a60e952a0fb3fd88e1d58eb01dbd1af29bb5` had an empty full Lean diff against
that source baseline at adoption. No new BASE tiling is claimed. `baseline-adoption.json`
retains the original timestamps/command/output verbatim.

| Measure | Adopted BASE | Fresh63 HEAD |
|---|---:|---:|
| Eligible source declarations | 1,956 | 1,948 |
| Directed candidates | 2,013 | 1,999 |
| Canonical reproduced characters | 646,340 | 646,318 |
| Proof-kind cross-file rows | 897 | 889 |
| Proof-kind same-file rows | 857 | 851 |
| Term-kind cross-file rows | 149 | 149 |
| Term-kind same-file rows | 110 | 110 |

Both full raw lists, all50 inert source inputs, reversible archives, blobs, requests,
output hashes and parser indexes are retained without caps. Same25 named source/citation
union as the preceding generation; no26th source or recursive-library-closure claim.
`pair-delta.json/out` and actual canonical `pairdiff.py` output retain all2new/16gone/13
changed scores. All31 dispositions are copied only after full raw-output/measurement
equality is verified. Direction is **a reproduces b**; denominator is the full canonical
b span. These are not compiler counts, debt-member counts or necessarily pure proof text.

The two new rows remain public isNil→private unary comparison89/167(shared application
of existing lenLe plus projection refolding), and SingleTape turn→end growth784/1564
(the previously reviewed phase family). Gone rows and thirteen changed scores are the
same as the earlier d0 comparison. In particular, longer identical guard adapters and
shorter map compatibility wrappers remain visible; no broad duplication waiver follows.

Source checks preserve all public/common private names, complete headers and visibility;
three old private concatenation helpers are replaced by three private Segment bridges.
No source term bodies or attributes change. Five public CounterLoop proof chunks change
(one primary composition consumer plus four older equation-reader repairs); public
statements remain textually frozen. The primary complete-header supplement handles nested
input defaults AND result-type let initializer assignments; initial bracket-only results
are retained with that limit explicit. This is source parsing, not a compiled census.

Fresh unmodified CLI lints on the same25 exact export files give153→153 style diagnostics
and campaign/check8b0FAIL/28WARN/28INFO→same. Full stdout/stderr and actual exits are retained;
there is no normalized new or gone diagnostic. These inherited findings are not waived.

The five-touched-file image sweep finds exactly two identical RAW public contracts:
SAT's helper already directly cites `Turing.FinTM.exists_comp_on_image`; Tautology rebuilds
the same existential computation with the same2*T1+T2+2 budget. The parent accepted its
standing mechanical same-PR repair. All15 candidate blocks, complete signatures and inline
closings are retained in `on-image-sweep-final.json/md`. Hardness.clNative_image instead
packages a different class-level partial-image polynomial premise; its seven client uses
are not another identical raw recipe. No exact class-row equivalence or new API necessity
was proved by this source-only sweep.

Seven accepted retention kinds remain limited to their actual canonical scope: clean
module/lifting; positive-release stop adapter; K-tape padding; finite one-way transducer;
polynomial bridge overhead; finite-family shared-bank dispatcher; and the separately
accepted existing unary-clock clean-call host/actual-orbit wrappers. Owner/window is
maintainer, next12.2c after activeMIG1 and before further SAT/Hardness fills. The named
retained lower bounds are SAT34/270 and Hardness49/544 (the latter is affected declarations,
not49 established exact duplicates). The16 closure/comparison implementation repairs are
separate retirements on merge; do not subtract them from the retained union. No new
API/import/future-host permission or image-class acknowledgment follows from these kinds.

Broader BASE expansion still has430 rows over the old9-file subgraph (51 from9→21,
379 from21→25). Old Catalog/Loop proof and definition correspondences, including exact
canonical id/const and near-complete host source, remain visible and are not all called
accepted debt, harmless client data or different T5 tables. The seven-kind ruling is not
blanket approval of these buckets. Earlier bounded baseline dispositions remain history,
not an exhaustive one-fifth census or current global clearance.

The unmodified screen can include following scope commands or suffixes of let-based
result types in its extracted spans. Raw scores are unadjusted; the complete-header
source supplement prevents that limitation from truncating the statement-freeze claim.
No alternate tiling, Lean elaboration, seal, axiom walk, replay, source/API/Git mutation,
cache/snapshot write, commit/push or gate closure was performed by this task.
`SHA256SUMS` freezes every other file in this historical generation.
'''
(OUT/'README.md').write_text(readme)
assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))
manifest=[]
for path in sorted(OUT.rglob('*')):
    if path.is_file() and path.name!='SHA256SUMS':manifest.append(sha(path.read_bytes())+'  '+str(path.relative_to(OUT)))
(OUT/'SHA256SUMS').write_text('\n'.join(manifest)+'\n')
for line in manifest:
    digest,path=line.split('  ',1);assert sha((OUT/path).read_bytes())==digest
print(json.dumps(dict(frozen_files=len(manifest),manifest_sha256=sha((OUT/'SHA256SUMS').read_bytes()),readme_sha256=sha((OUT/'README.md').read_bytes())),indent=2))
