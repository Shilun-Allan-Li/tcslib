from pathlib import Path
import sys,json,hashlib,shutil,collections,subprocess
sys.dont_write_bytecode=True
E=Path('/private/tmp/ab34-fe-live1-final-validation/evidence');D=E/'first-None-census';D.mkdir(exist_ok=True);OLD=Path('/private/tmp/ab34-overnight-fe1/EXPORT');F=Path('/Users/seyoonr/.codex/worktrees/ab34-followup-api/tcslib-arora-barak-ch3-4');sys.path.insert(0,str(E/'helpers/devtools/seyoon'));from graph import imports_of
rows=json.loads((OLD/'DISPOSITIONS.json').read_text());chosen=[r for r in rows if 'first None halt' in r['disposition']];exclusions=[r for r in rows if 'nondeterministic' in r['disposition'] or r['id']==71]
api='Turing.MultiTapeTM.exists_first_halt';target='TCSlib.Complexity.TuringMachine.Finite';graph={str(p.relative_to(F))[:-5].replace('/','.'):imports_of(p) for p in (F/'TCSlib').rglob('*.lean')}
def chain(m):
 q=collections.deque([[m]]);seen=set()
 while q:
  p=q.popleft();n=p[-1]
  if n==target:return p
  if n in seen:continue
  seen.add(n)
  q.extend(p+[k] for k in graph.get(n,[]) if k.startswith('TCSlib.'))
 return None
notes={
9:'Exact existing helper contract: apply exists_first_halt tm cfg h. Its full-configuration equality is already the required endpoint.',
16:'Apply the canonical theorem to M.tm at each unary input and deadline T n; choose the resulting witnesses as the function τ. Retain b2_unary_run and output packaging. Full endpoint equality supplies state/output at τ; prefix exclusion transfers through the existing unary relation.',
17:'Apply to V.tm, V.tm.initCfg y, and deadline T from hV. Retain choice-word splitting, b2_verify_run/finish, and output_unique packaging; use canonical prefix exclusion and endpoint state at the selected t.',
18:'Apply to M.tm.initCfg at the existing ComputesInTime deadline. Preserve state and output through the canonical complete endpoint equality; the caller statement remains unchanged.',
19:'Apply to its arbitrary decider configuration and known halt deadline. Retain the existing initial nonhalt premise to prove selected time positive; use complete endpoint equality for its required final result.',
33:'Same positive-time arbitrary-configuration route as sat_call_first_halt, with existing initial exclusion retained. No new first-live premise.',
47:'Replace only the local T := Nat.find halt cut with canonical T≤t, prefix exclusion, and complete endpoint equality. Preserve the configuration-count injection/cardinality/space proof and stationary extension to configBound.',
50:'Apply to D and dc0 at deadline T using hTh. Keep the existing proof that dc0 starts live to establish T0>0, and retain all simulation, head/framing, and output packaging.',
51:'Apply to M at Cfg.init q V and deadline T using hT. The theorem accepts an arbitrary configuration, so the local retagged M\' is irrelevant to the selector; retain it where later visited-head bounds use it. Keep the cleaning/framing proof.',
52:'Apply to tm at tm.initCfg x and deadline T. Re-express the result using local run notation. Keep the cell/counting bound and stationary tail proof; no generalized API is needed for the selector.',
54:'Apply to K.tm at K.tm.initCfg x and deadline tK from hK. Keep buffer/rewind setup and output_unique. Mechanical edit authority for colleague-owned ClockMachine remains a separate ownership check, not an API issue.',
58:'Apply to the deterministic boot machine S.tm at deadline T from hS. Retain the NDTM host choice-word boot/rewind packaging; the minimized run itself is deterministic, so this belongs in the deterministic selector list.',
76:'Canonical home, not a consumer copy. Retain Nat.find inside the public theorem itself.',
82:'Apply to (maskedClock W false).tm at deadline b*(T x.length+1), using existing hm/hhalt. Retain clockStageCfg_run and output_unique. The complete endpoint equality supplies halted state/output at τ.',
83:'Apply in the positive-k branch to M.tm at deadline T x.length. Keep the sweep simulation and quadratic-time arithmetic; canonical equality transfers output at τ.',
84:'Apply to M.tm at input y=x.map(dgRetract a0), deadline T y.length. Keep dg_simulate, window/span, and space proof; use canonical prefix exclusion and endpoint equality for the local cut.',
85:'Apply to M.tm at the known halted deadline T. Use canonical equality (in the required orientation) for timedCapturedCfg and prefix exclusion for timedCapture_run; preserve the t+1 bound.',
86:'Apply to M.tm at the known halted deadline T. Use canonical equality for universalCapturedCfg and prefix exclusion for universalCapture_run; preserve the t+1 bound.'}
result=[]
for r in chosen:
 r=dict(r);p=OLD/r['block'];b=p.read_bytes();source=(F/r['path']).read_bytes();assert source.count(b)==1,(r['id'],r['name'],'source changed inside inspected chunk');c=chain(r['path'][:-5].replace('/','.'));assert c is not None,(r['id'],'Finite not already imported')
 d=D/r['block'];d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b);r.update({'canonical_API':api,'route_status':'canonical home; no replacement' if r['id']==76 else 'same existing public API; source-inspected route, not a new elaborated draft','route':notes[r['id']],'existing_import_chain_to_Finite':c,'new_import_needed':False,'new_statement_name_API_home_or_design_needed_for_selector':False,'current_F1_source_head':'a93d1867d6ed9700f2fd89a28092e39a45db2dd2','complete_chunk_literal_unchanged_in_current_F1':True,'current_line':source[:source.index(b)].count(b'\n')+1,'current_owner_source_sha256':hashlib.sha256(source).hexdigest(),'chunk_bytes':len(b),'chunk_sha256':hashlib.sha256(b).hexdigest(),'new_Lean_probe_or_patch':False});result.append(r)
excluded=[]
for r in exclusions:
 b=(OLD/r['block']).read_bytes();d=D/r['block'];d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(b);excluded.append({k:r[k] for k in ['id','path','name','block','disposition','reason','chunk_sha256']})
(D/'DETERMINISTIC-FIRST-NONE.json').write_text(json.dumps(result,indent=2)+'\n');(D/'NONMATCHING-EXCLUSIONS.json').write_text(json.dumps(excluded,indent=2)+'\n')
text='Inspected deterministic first-None selector reuse from the frozen90 FE dispositions\n\nThis is a source-census reuse, with no new Lean execution, patch, or global absence claim. There are18 inspected rows: canonical Finite.exists_first_halt plus17 consumers. All17 already import Finite transitively and match the existing public theorem for the selector. Surrounding output, positivity, simulation, head, clock, and space arguments remain caller packaging; this report does not propose replacing them wholesale. Parent already owns the four helper bodies EXP.enumCont_first_halt, SAT.sat_first_halt/sat_call_first_halt and Hardness.clA5_call_first_halt. The additional13 are listed below. Every complete source chunk and current source hash is retained. Full per-site route/premise/import status is in DETERMINISTIC-FIRST-NONE.json. These source-inspected routes are not new native or sealed checks.\n\n'
for r in result:
 text+=f"- {r['path']}:{r['current_line']} — {r['name']}: {r['route']}\n"
text+='\nNONMATCHING-EXCLUSIONS.json retains four nondeterministic runWith/HaltsWithin selectors and the mixed physical-None/live WindowRun minimum, with complete chunks. Their contracts are not the deterministic first-None theorem. The canonical Nat.find implementation is retained at home. Colleague file ownership remains a separate integration check. Only this inspected lower bound is claimed.\n';(D/'REVIEW.md').write_text(text)
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['MANIFEST.json','SHA256SUMS']:files.append({'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
manifest={'source_dispositions':str(OLD/'DISPOSITIONS.json'),'source_dispositions_sha256':hashlib.sha256((OLD/'DISPOSITIONS.json').read_bytes()).hexdigest(),'source_baseline':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','current_F1_head':subprocess.check_output(['git','-C',str(F),'rev-parse','HEAD'],text=True).strip(),'inspected_deterministic_rows':18,'canonical_home_rows':1,'consumer_rows':17,'new_route_probes':0,'files':files};(D/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n');(D/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in files)+hashlib.sha256((D/'MANIFEST.json').read_bytes()).hexdigest()+'  MANIFEST.json\n');print(json.dumps({'folder':str(D),'files':len(files),'REVIEW_sha256':hashlib.sha256((D/'REVIEW.md').read_bytes()).hexdigest(),'MANIFEST_sha256':hashlib.sha256((D/'MANIFEST.json').read_bytes()).hexdigest()}))
