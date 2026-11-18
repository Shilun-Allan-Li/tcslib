# io-sprg current checkpoint report assembler. Reads source/gate evidence only; no Lean.
import csv,difflib,hashlib,json,pathlib,re,subprocess,runpy
P=pathlib.Path;root=P.cwd();parts=root/'evidence/review/m0-report-sp-w2'
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
previous='1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0';base='5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
files=[m+'.lean' for m in(root/'evidence/logs/fillinputs-inverse-api/owners.txt').read_text().splitlines()]
line_maps={}
for f in files:
 old=subprocess.check_output(['git','show',previous+':'+f],text=True).splitlines();new=(root/f).read_text().splitlines();mapping={}
 for a,b,n in difflib.SequenceMatcher(a=old,b=new,autojunk=False).get_matching_blocks():
  for j in range(n):mapping[a+j+1]=b+j+1
 for i,l in enumerate(old,1):
  if i not in mapping and new.count(l)==1:mapping[i]=new.index(l)+1
 line_maps[f]=mapping
unresolved=[]
def update_text(text):
 text=text.replace('`fidelity-declarations.tsv`','`evidence/statements/fidelity-current.tsv`').replace('`proof-obligations.tsv`','`evidence/statements/proof-obligations-current.tsv`')
 text=text.replace(previous,previous+' (review snapshot; line references remapped by root to '+head+')').replace('5,899','{:,}'.format(sum(len((root/f).read_text().splitlines()) for f in files))).replace('300,480','{:,}'.format(sum((root/f).stat().st_size for f in files)))
 def replace(m):
  short=m[1];n=int(m[2]);matches=[f for f in files if f.endswith('/StructuredSeed/'+short)] if '/' not in short else []
  if not matches:matches=[f for f in files if f.endswith('/'+short) or f==short]
  if len(matches)!=1:return m[0]
  f=matches[0]
  if n not in line_maps[f]:unresolved.append(dict(file=f,line=n));return m[0]
  return short+':'+str(line_maps[f][n])
 lines=[]
 for line in text.splitlines(keepends=True):
  context=[None]
  pattern=r'((?:Reductions/|Claim42/)?[A-Za-z0-9_]+\.lean):(\d+)|`:(\d+)`'
  def token(m):
   if m[1]:
    matches=[f for f in files if f.endswith('/StructuredSeed/'+m[1])] if '/' not in m[1] else []
    if not matches:matches=[f for f in files if f.endswith('/'+m[1]) or f==m[1]]
    context[0]=matches[0] if len(matches)==1 else None
    return replace(m)
   f=context[0];n=int(m[3])
   if f is None:return m[0]
   if n not in line_maps[f]:unresolved.append(dict(file=f,line=n,short=True));return m[0]
   return '`:'+str(line_maps[f][n])+'`'
  lines.append(re.sub(pattern,token,line))
 return ''.join(lines)
checks=[]
rs={}
for folder in ['m0-final-candidate','m0-floor-root','m0-seal-reader-repair-final','m0-sp-w2','m0-inverse-api','m0-eval-seal-repair','m0-sp-w3']:
 for l in(root/'evidence/build'/folder/'results.jsonl').read_text().splitlines():
  r=json.loads(l)
  if r['module'].startswith('TCSlib/Cryptography/Obfuscation'):rs[r['module']]=r
for m,r in rs.items():assert hashlib.sha256((root/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256'] and r['rc']==r['errors']==r['error_forms']==0
seals={}
for l in(root/'evidence/rule10/m0_final/seal-runs/results.jsonl').read_text().splitlines():
 r=json.loads(l)
 if 'module'in r:seals[r['module']]=r
bind=runpy.run_path(str(root/'evidence/tools/io-sprg-rule10/environment_binding.py'))
environment=bind['snapshot'](root/'.lake/io-sprg-oleans',root/'evidence/rule10/m0_final')
passing=[m for m,r in seals.items() if (b:=bind['previous'](root/'evidence/rule10/m0_final/seal-environment-bindings.jsonl',m)) and b['environment_sha256']==environment and b['log_sha256']==r['log_sha256'] and r['rc']==r['errors']==0 and (root/(m+'.lean')).exists() and hashlib.sha256((root/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256']]
controls={}
if (root/'evidence/rule10/m0_final/control-runs/results.jsonl').exists():
 for l in(root/'evidence/rule10/m0_final/control-runs/results.jsonl').read_text().splitlines():
  r=json.loads(l)
  if 'module'in r:controls[r['module']]=r
control_expectations={}
for variant in ['coe-A','coe-B','strict-A','strict-B']:
 for plan in json.loads((root/'evidence/rule10/m0_final/controls'/variant/'controls-plan.json').read_text()):
  errors=sum(c['negative'] for c in plan['controls']) if plan['sealed'] else 0
  control_expectations[plan['module']]=(int(errors>0),errors)
control_passing=[]
for m,r in controls.items():
 b=bind['previous'](root/'evidence/rule10/m0_final/control-environment-bindings.jsonl',m)
 if (r['rc'],r['errors'])==control_expectations.get(m) and b and b['environment_sha256']==environment and b['log_sha256']==r['log_sha256'] and (root/(m+'.lean')).exists() and hashlib.sha256((root/(m+'.lean')).read_bytes()).hexdigest()==r['source_sha256']:
  control_passing.append(m)
unsealed_count=sum('/ControlU_'in m for m in control_passing)
sealed_count=sum('/ControlS_'in m for m in control_passing)
header=f'''# io-sprg Phase A — M0 gates in progress

M0 is not frozen or delivered. All22new owners elaborate at their current source bytes;
146 named proof holes remain. Canonical seals and paired controls are still being completed.
No exchange push has occurred. This report distinguishes proved readers, M0 theorem holes,
and untested staged proof candidates.

## Bases, heads, and milestones

- Lean base: `{base}`.
- Current local fill/io-sprg head: `{head}`.
- Records: `dbea2807532392781304e004715f3b0190025f5e`.
- Host inputs: `bc9d982b83cb35ea351e2fb373752e8688945b1c`.
- Rule10 source tools: `2467bc3befdad8472b1f359337bf3a203e3651e1`.
- M0: gates in progress. M1–M6: proof milestones pending. Phase B is outside scope.
- New source:22files; existing edit: root TCSlib.lean, one export import.

## Current checks

| Check | Current evidence |
| --- | --- |
| Owned-module elaboration |22passing current source hashes; rc0, errors0 in both forms; no non-sorry source warnings. |
| Public source declarations |670ADDED,0CHANGED,0REMOVED against the base. |
| Stored constants / typed dump |1036stored;948public kernel types. Latest full collector and kernel census follow the disclosed SP-W3 non-vacuity repair. |
| Axioms |511public theorem prints match the full graph; only propext, Classical.choice, Quot.sound and M0 sorryAx.146direct holes,265transitive dependents. |
| Canonical/diagnostic seal matrix |{len(passing)}current-environment passing probes of88. {'Complete.' if len(passing)==88 else 'Completion is pending.'} |
| Unsealed controls |{unsealed_count}/48current environment-bound unsealed probes passed; {sealed_count}/48sealed probes have expected aggregate outcomes so far. Exact per-control validation follows the queue. |
| Explicit-unfold scan |21items, all actual theorems;0foreign TCSlib or Core/Mathlib definitions. Exported comp_map resolves to LawfulFunctor.comp_map. |
| Style/campaign/sk15 |Style0findings;0new individual campaign FAIL/WARN against base. sk15rc0 with one lexical finding: a 15-line reader statement whose proof is Iff.rfl, triaged in sk15-triage.txt. |
| Widths |Every new file≤1000lines and every line≤100characters; exact per-file inventory attached. |
| Clash scan |Current670name scan:0clashes/duplicates. |
| Cache |83explicit direct Mathlib roots; latest narrowed refresh passed under-k3. |
| Replay |Seven-commit draft replay passed; final complete replay/bundle/manifests pending. Empty marker replay also reproduced its exact hash. |

## Source and host

jls26.pdf was read in place only after SHA-256 matched
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
No PDF is copied, committed, or delivered. Base/head tree checks found no PDF paths.

Initial memory headroom3.918167GiB failed the4GiB floor; the delayed retry passed at
4.368317GiB. Disk95.748741GiB exceeded12GiB; hardware12CPUs/18GiB RAM.
The initial preflight log is dated08:48:10UTC and the successful retry08:58:49UTC,
more than ten minutes later. Wrapper acquisitions/releases and recorded dead-wrapper
reaps are attached; their audit does not invent unlogged wait or termination times.
The host limit is “at most3Lean processes across ALL jobs”; io-sprg holds at most one.
Root runs every Lean/lake/probe/seal through the exact pinned lean-slot.sh with
LEAN_SLOT_TAG=io-sprg. Narrowed cache alone holds-k3. No lake build or unfiltered
cache fetch ran. The user explicitly authorized the dispatch's slot-wrapped shell checks
over the generic AGENTS.md prohibition; its initial automatic-review rejection is resolved.

**Team-limit deviation.** A child started a third research descendant, exceeding the
whole-job two-subagent limit. Root interrupted it on discovery and prohibited further
spawning/resumption. Its recorded activity was source reading, rg, and temporary notes;
no Lean, Lake, cache, push, or implementation-source mutation was reported. This is based
on the parent's task/activity context, not an independent process-history audit. Duration
was not established. The breach and correction are in evidence/host/team-limit-correction.json.
The active team is now root plus the two original children; the extra descendant stays stopped.
Tagged slot history is attached in evidence/host/slots-io-sprg.log. Its wrapper-event
audit accounts for dead-wrapper REAP records before new acquisitions. One historical
wrapper has a REAP without a RELEASE; its end time, termination cause, and child-process
history are not inferred. This is not an independent audit of all host processes.

## Statement changes and judgment calls

There is no post-M0 statement change because no freeze exists yet. SP-W1 is resolved by
the user's exact ruling: “Use rational δ throughout, coercing it to real values for analysis”.
SP-W2 repairs two false free-oracle syntax equalities at acceptance-probability level;
its exact obligations, four-vs-five-query counterexample, minimal change, and authorization
are in evidence/route-requests/SP-W2.txt. No algorithm or headline security inequality changes.
SP-W3 strengthens HasPolyStretch by requiring eventual kappa<=seedBits, ruling out
zero/constant-length existential witnesses. The actual construction has the stronger
all-parameter bound kappa+1<=seedBits; no hypothesis or algorithm changes.

Additional pre-M0 choices: faithful injective index/draw encodings; explicit finite
coordinates; optional empty-grid bucket positions; complete public parameter words;
canonical assumption challenge encodings; one T6 sampler/map before all schedules;
precise reuse imports for existing floor and bounded-inverse APIs. These are detailed below.
Proof-plan review found public PadQuad.exists_pow_dominates in an unavailable broader
owner. The proposed copy of its monic-normalization argument is marked superseded,
not approved or landed. The preferred untested stretch plan keeps the polynomial
coefficient and composes existing rpow growth facts to absorb it. No import changed.
No open approval or user-input question remains.

## Tool adaptations and evidence integrity

The reviewed runner's Linux flock was replaced by the pinned Mac slot wrapper and own
package/olean paths. Chunk size2048 preserves every requested name while avoiding repeated
whole-environment scans. Success records use IO.println of the same MessageData.toString;
the adapter verifies that reversing this transport restores every other byte and line count.
Every guard, instance mask, exact lookup-state check, component identity and EOF check remains.
Queues now bind every reused pass to the complete job-owned olean environment as well as
probe/log hashes. The SP-W3 change invalidated historical environment-free passes; all
current gates are rerun. No historical pass is represented as a current environment-bound pass.
The original1154-request pilot passed, and the faster equivalent pilot passed in53.29seconds
versus250.75seconds. Unsealed control syntax uses outer@ to suppress implicit lambdas;
positives use published readers and negatives use reflexivity under the stored telescope.
The wrapper archives failure probes/logs by hash. An overwritten old failed log was reproduced
exactly from its saved probe, matching its original SHA-256; this is explicitly dated evidence.

## Open questions

- SP-W1: resolved; recommended/selected option is rational delta with real analytic coercions.
- SP-W3: resolved under the same autonomy authorization; growing-seed stretch is selected.
- SP-W2: resolved under the user's autonomous-judgment authorization; recommended/selected
  option is acceptance equality. Adding dummy sampling to the algorithms was rejected.
- Source folder and shell-check exception: supplied/approved by the user; no pending request.

'''
body='\n\n'.join(update_text((parts/name).read_text()) for name in ['fidelity.md','primitive-nonvacuity.md','helper-plan.md','disclosures.md','sp-w2.md','status-and-size.md'])
(root/'evidence/REPORT.md').write_text(header+body+'\n')
(root/'evidence/review/report-line-remap.json').write_text(json.dumps(dict(previous=previous,current=head,unresolved=unresolved),indent=2)+'\n')
print(json.dumps(dict(head=head,owner_checks=len(rs),current_seal_passes=len(passing),line_remap_unresolved=len(unresolved))))
