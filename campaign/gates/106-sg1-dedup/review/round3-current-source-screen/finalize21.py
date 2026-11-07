"""Freeze the complete, historical21 generation; final25 is a separate sibling."""
from pathlib import Path
import base64, collections, datetime, hashlib, io, json, subprocess, tarfile

OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[4]
def sha(b):return hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def save(name,x):(OUT/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
c=json.loads((OUT/'capture.json').read_text());d=json.loads((OUT/'pair-delta.json').read_text())
assert c['base']=='3023dc1408c3d216fc07a7cbba9ae30135b861ed'
assert c['head']=='d0c4a292e781b55617e05b33fdd423bb059fd735'
assert len(c['population'])==21
for commit in [c['base'],c['head']]:
    assert git('rev-parse',commit).decode().strip()==commit
    assert git('cat-file','-t',commit).strip()==b'commit'
for side in ['base','head']:
    raw=base64.b64decode((OUT/(side+'.tar.base64.txt')).read_bytes())
    assert sha(raw)==c['sides'][side]['archive_sha256'] and len(raw)==c['sides'][side]['archive_bytes']
    with tarfile.open(fileobj=io.BytesIO(raw)) as tar:
        members={m.name for m in tar.getmembers() if m.isfile()}
        assert members==set(c['population'])
        for row in c['sides'][side]['files']:
            b=(OUT/'inputs'/side/(row['path']+'.txt')).read_bytes()
            assert tar.extractfile(row['path']).read()==b==git('show',c[side]+':'+row['path'])
            assert len(b)==row['bytes'] and sha(b)==row['sha256']
            assert git('rev-parse',c[side]+':'+row['path']).decode().strip()==row['blob']
            assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['blob']
    receipt=json.loads((OUT/(side+'-run.json')).read_text());output=(OUT/(side+'.out')).read_bytes()
    assert receipt['exit']==0 and receipt['output_sha256']==sha(output) and receipt['bytes']==len(output)
    assert receipt['full_population']==21 and receipt['command'][7:]==list(c['population'])
    assert receipt['command'][:5]==['nice','-n','10','python3','-I']
    schedule=json.loads((OUT/('scheduling-check-'+side+'.json')).read_text())
    assert schedule['exit']==0 and int(schedule['actual_process_snapshot'].split()[1])==10
    rows=json.loads((OUT/(side+'-candidates.json')).read_text())
    ix={r['label']:r for r in json.loads((OUT/(side+'-index.json')).read_text())}
    assert len(rows)==d[side]['candidates'] and len(ix)==d[side]['declarations']
    assert len({(r['a'],r['b']) for r in rows})==len(rows)
    assert sum(r['shared'] for r in rows)==d[side]['reproduced_chars']
    assert all(r['denominator']==ix[r['b']]['body_chars'] for r in rows)
tool='scripts/copy-text-screen-v3.py';b=(ROOT/tool).read_bytes()
assert sha(b)==c['tools'][tool]=='f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181'
assert b==(OUT/'tools/copy-text-screen-v3.py.txt').read_bytes()==git('show',c['base']+':'+tool)==git('show',c['head']+':'+tool)
events=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
assert [r['event'] for r in events]==['waiting','acquired','released']
br=json.loads((OUT/'base-run.json').read_text());hr=json.loads((OUT/'head-run.json').read_text())
assert events[1]['utc']<=br['start_utc']<=br['end_utc']<=hr['start_utc']<=hr['end_utc']<=events[2]['utc']
assert (d['base']['candidates'],d['head']['candidates'])==(1634,1619)
assert len(d['new'])==1 and len(d['gone'])==16 and len(d['changed_measurements'])==13

prior=json.loads((OUT.parent/'round2-current/context.json').read_text())
links=[]
for path in ['TCSlib/Complexity/ClassNP/Tautology.lean','TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean','TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean']:
    row=next(x for x in c['sides']['head']['files'] if x['path']==path)
    assert row['sha256']==prior['source_pins'][path]['head_sha256']
    assert git('show',prior['supplied_frozen_head']+':'+path)==(OUT/'inputs/head'/(path+'.txt')).read_bytes()
    links.append(dict(path=path,sha256=row['sha256'],historical_head=prior['supplied_frozen_head'],current_head=c['head']))
save('historical-unchanged-source-linkage.json',links)

new=d['new'][0]
assert (new['a'],new['b'],new['shared'],new['denominator'])==('SingleTape.lean::dg_turn_with_growth','SingleTape.lean::dg_end_with_growth',784,1564)
classifications=[dict(change='new',row=new,group='G1: retained growth-phase proof family',assessment='The same directed edge and exact source bodies already occur in immutable round2 HEAD. Material transition/frame scaffold in distinct turn/end phases; public Segment composition now replaces the old private concatenator. It remains a real candidate and does not establish permanent-debt approval.')]
for row in d['gone']:
    if row['b']=='Tautology.lean::tautDual_segment_add':
        group='G2: removed private concatenation proof'
        assessment='Actual private composition theorem deleted; consumers use Segment.trans. Retirement/accounting occurs on merge, not this screen.'
    elif 'clNative_map' in [row['a'].split('::')[-1],row['b'].split('::')[-1]]:
        group='G3: map witness delegated to published API'
        assessment='Old private/public arithmetic rederivation candidate disappears. New private compatibility wrapper has176chars and calls the public closure through its published equation; it is not deleted.'
    elif 'clNative_linear' in [row['a'].split('::')[-1],row['b'].split('::')[-1]]:
        group='G4: short linear wrapper'
        assessment='Old63-character duplicate is replaced by36-character direct public theorem use, below v3 threshold. Name/header survive; no compiler declaration deletion is inferred.'
    elif row['b']=='Hardness.lean::clA5Drop_native':
        group='G5: changed drop compatibility proof'
        assessment='New body composes the published prefix-dropping closure; this old same-file fragment no longer crosses the candidate threshold. This is a measurement change, not deletion or an automatic debt-member retirement.'
    else:
        group='G6: shortened pairing/append wrappers'
        assessment='Surviving private adapter proofs now delegate to published pairing/append contracts; at least one body becomes too short for the old edge. Exact old/new bodies and thresholds are retained. Candidate removal is not a count of deleted declarations or a global debt waiver.'
    classifications.append(dict(change='gone',row=row,group=group,assessment=assessment))
for entry in d['changed_measurements']:
    row=entry['head'];pair={row['a'],row['b']}
    if all(x.startswith('CounterLoop.lean::') for x in pair):
        group='G7: public segment equation at existing witnesses'
        assessment='Four reciprocal done/escape and trajectory scores grow by public segment_iff use; exact source equals audited round2 HEAD.'
    elif any('guard_add' in x for x in pair):
        group='G8: shared Segment compatibility adapter'
        assessment='Both generic private cut adapters now construct/read public Segment contracts and call Segment.trans. Overlap grows127/127→525/525 in both directions; retain the increase rather than calling it removed text. Generic adapter/debt accounting remains parent-owned.'
    elif any('clNative_map' in x or 'sat_pt_mapSnd' in x for x in pair):
        group='G9: identical public-map compatibility wrappers'
        assessment='Shared arithmetic drops279chars→176chars while coverage rises to100% because both wrappers now use the same published closure/equation. Their old names/headers remain; thin adapter similarity is explicitly visible, not a new implementation or a permanent-debt acknowledgement.'
    elif all(x.startswith('SingleTape.lean::') for x in pair):
        group='G1: retained growth-phase proof family'
        assessment='Reciprocal of the sole new edge. Existing phase scaffold and source are identical to round2 HEAD; raw736/1283→784/1331 remains explicit.'
    else:
        assert all(x.startswith('Tautology.lean::') for x in pair)
        group='G10: public composition at existing dual phases'
        assessment='Four scan/copy or valid/invalid scores change through public Segment bridge/composition. Exact full source equals round2 HEAD; distinct phase statements remain.'
    classifications.append(dict(change='changed',row=entry,group=group,assessment=assessment))
assert len(classifications)==30
save('head-delta-classification.json',dict(scope='Every1new/16gone/13changed directed measurement, source-level bounded classification. No global legacy/debt acceptance.',rows=classifications))
new_chars=sum(r['shared'] for r in d['new']);gone_chars=sum(r['shared'] for r in d['gone']);changed_chars=sum(r['head']['shared']-r['base']['shared'] for r in d['changed_measurements'])
assert new_chars-gone_chars+changed_chars==d['head']['reproduced_chars']-d['base']['reproduced_chars']==-111
save('score-accounting.json',dict(new_shared_chars=new_chars,gone_shared_chars=gone_chars,retained_shared_delta=changed_chars,net_chars=-111,directed_scores_not_debt_counts=True))
assert not list(OUT.rglob('*.lean')) and not list(OUT.rglob('*.pyc'))
save('final-verification.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),generation='HISTORICAL21; superseded in source coverage before issue by separate full25 generation',exact_source_inputs=42,complete_archives=2,full_source_population=21,screen_exits=[0,0],screens_serial=True,lock_released=True,niceness_observed=[10,10],all_raw_rows_reconciled=True,head_delta_rows_classified=30,expanded_baseline_rows_classified=51,no_lean_git_source_cache_mutation=True,diagnostic_failure='Initial sandboxed ps inspection failed; diagnostic-attempt1.json discloses uncaptured original terminal traceback and subsequent successful escalated snapshots. No screen failed.'))
newtext='\n'.join('- **'+str(r['change'])+' / '+r['group']+'**: '+r['assessment'] for r in classifications if r['change']=='new')
readme='''# Gate106 round3 historical21-file generation

Both complete, unmodified21-file BASE/HEAD screens passed and released the shared lock.
This generation is **historical**, superseded before issue by the separate required
`../round3-current-source-screen25/` generation, which includes four further API comparison
homes. It is not the final gate source population, dispatch readiness or gate clearance.

Pins: base`3023dc1408c3d216fc07a7cbba9ae30135b861ed`; head
`d0c4a292e781b55617e05b33fdd423bb059fd735`. All42 exact source inputs, both reversible
full archives, full Git commit/blob hashes, import lines, five-file diff and unmodified
tool bytes are retained. `POPULATION.md`/`population.txt` explain the full named union.
No screen or candidate was capped. This is not a recursive library import-closure claim.

| Measure | BASE21 | HEAD21 |
|---|---:|---:|
| Eligible declarations | 1,714 | 1,706 |
| Directed candidates | 1,634 | 1,619 |
| Reproduced normalized chars | 499,531 | 499,420 |
| Proof / cross-file | 658 | 649 |
| Proof / same-file | 766 | 760 |
| Term / cross-file | 110 | 110 |
| Term / same-file | 100 | 100 |
| Wall seconds | 744.274 | 689.445 |

BASE ran22:06:21–22:18:45UTC; HEAD22:18:45–22:30:15UTC on2026-11-07.
Both commands used nice10/Python-I and one continuous shared screen lock. Actual process
snapshots independently observed ni10. Raw stdout includes stderr and parses completely;
run receipts retain exits, commands, timestamps, hashes, CPU and raw cumulative child
max-RSS values (not a per-run peak claim). One initial sandboxed `ps` diagnostic failed;
its terminal error/retention limit is disclosed in `diagnostic-attempt1.json`, followed
by successful escalated process snapshots. It was not a failed screen or proof check.

The old nine-file BASE subgraph is exactly1,583pairs/492,990chars, with every historical
edge and score identical. Widening to21 exposes51 further BASE rows; it is not51 new
head duplicates. `population-expansion-accounting.json` preserves all51; all have bounded
source dispositions in17groups in `expanded-baseline-classification.json`, with every
endpoint body retained. Material existing watches include public/private live-prefix,
input trajectory and first-halt arguments. No acknowledgement of those or all legacy
candidate families is inferred. Short direction/update and model-term patterns are
separated from substantial proof similarities; scope-command tails remain explicit.

BASE→HEAD has1new,16gone and13changed retained measurements. All30 are individually
dispositioned in `head-delta-classification.json`; full raw/JSON lists and complete
pair delta are retained. Tool direction is **a reproduces b**; denominator is the full
canonical normalized **b** span. These directed rows are not debt-member counts.

'''+newtext+'''

The new SingleTape edge is784/1,564(50%), with its reciprocal736/1,283→784/1,331.
The three changed consumer homes Tautology/CounterLoop/SingleTape are byte-identical to
the immutable round2 head, as independently checked in
`historical-unchanged-source-linkage.json`. Existing distinct phase statements and
material common scaffold remain visible; there is no new debt waiver.

Of the gone rows, one concerns the actually deleted private Tautology concatenation
proof; four expose old public/private linear-map witness rederivations now delegated to
published APIs. Most other disappearances follow shorter surviving append/pair adapters,
and one follows a changed drop-closure proof. A disappearing edge is not a deleted
compiler constant. The thirteen changed scores include four CounterLoop uses of
segment_iff, four Tautology phase-composition scores, two identical Segment guard adapters
growing127→525chars, two public-map compatibility wrappers shrinking279→176sharedchars
while reaching100%, and the SingleTape reciprocal. The net directed score change is
only−111chars; `score-accounting.json` retains the exact contribution breakdown.

The source-only historical comparison confirms exactly16 SAT/Hardness proof re-points
from round2, preserving depth-aware normalized declaration names/kinds/headers in those
two files. Ten formerly eligible adapters become shorter than60chars; one other changed
adapter was already below the threshold. They remain source declarations. All382 eligible
term bodies are identical BASE/HEAD; this does not purport to enumerate short bodies or
compiled auxiliaries. `parser-delta.json` distinguishes the source/eligibility effects.

Canonical span limits are preserved, not silently repaired: CounterProg update proofs
can include a following `omit ... in` directive, and some final declaration spans include
`end`/`open` commands. `parser-scope-tail-limit.json` identifies actual instances and
separates those characters in semantic review while retaining every raw denominator.
No alternative tiling run or adjusted score is substituted.

No Lean/replay, source/API/Git mutation, cache/snapshot write, commit/push, dispatch,
debt approval or gate closure was performed. Parent owns the ledger and final25 packet.
The folder is frozen after exact-source/output QA; SHA256SUMS covers every other file.
'''
(OUT/'README.md').write_text(readme)
lines=[]
for path in sorted(OUT.rglob('*')):
    if path.is_file() and path.name!='SHA256SUMS':lines.append(sha(path.read_bytes())+'  '+str(path.relative_to(OUT)))
(OUT/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
for line in lines:
    digest,path=line.split('  ',1);assert sha((OUT/path).read_bytes())==digest
print(json.dumps(dict(frozen_files=len(lines),manifest_sha256=sha((OUT/'SHA256SUMS').read_bytes()),readme_sha256=sha((OUT/'README.md').read_bytes())),indent=2))
