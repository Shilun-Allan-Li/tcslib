"""Prepare comment-only source and postmerge registry patches; never apply to the worktree."""
from pathlib import Path
import sys,importlib.util,contextlib,io,json,re,difflib,hashlib,textwrap
sys.dont_write_bytecode=True
out=Path(__file__).resolve().parent;root=out.parents[4];spec=importlib.util.spec_from_file_location('r',out/'source_review.py');R=importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):spec.loader.exec_module(R)
proposed={};edits=[]
def replace(f,a,b,reason):
 s=proposed.get(f,R.STAGES['current'][f]);assert s.count(a)==1,(f,a[:90],s.count(a));proposed[f]=s.replace(a,b,1);edits.append({'path':f,'reason':reason,'before':a,'after':b})
f='TCSlib/Complexity/TuringMachine/Build/Catalog.lean'
replace(f,'''The R3 increment of the machine-construction library
(`machine-library-design.md` §12): the remaining audited A-chain tape
routines promoted as public machines with exact time **and** space costs,
plus the space retro-annotation of the existing catalog and control
surface. Per frozen decision 12.2 this lives in a **new** file — the new
rows and the space lemmas for the old rows both — keeping
`Build/Primitives.lean` byte-identical; the later refactor toward a
per-theme layout is a recorded backlog item.''','''This module collects tape routines with exact time **and** space costs,
plus space annotations for the functional catalog and control surface.
Named function witnesses and their intrinsic specifications live in their
construction modules, including `Build/Primitives.lean`; the corresponding
existential time-and-space rows are packaged here.''','Remove obsolete byte-identity claim and describe current homes.')
f='TCSlib/Complexity/TuringMachine/Simulation.lean'
replace(f,'''assembled from these. Everything here is public — it is shared
audited surface — and carries no finiteness assumptions beyond what each
gadget needs.''','''assembled from these. The constructions and their specification API are
public shared surface, with local proof helpers for their intrinsic bounds.
Each gadget carries only the finiteness assumptions it needs.''','Distinguish the public construction API from the three new private ledger helpers.')
f='TCSlib/Complexity/TuringMachine/Build/Primitives.lean'
replace(f,'''`TCSlib.Complexity.TuringMachine.Composition`, the contracts are
existentially packaged; each fill implements a named private machine with
its run invariants and closes the existential.''','''`TCSlib.Complexity.TuringMachine.Composition`, the convenience rows package
public named witnesses with their run specifications. Private helpers establish
the local invariants used by those specifications.''','Describe the current public-witness/convenience-row organization.')
replace(f,'## Named witnesses and their specs (MIG-1)','## Named witnesses and their specs','Keep the module index about declarations.')
replace(f,'''* `unaryTokenTM` (`unaryTokenTM_computes`), `appendBitTM` (`appendBitTM_computes`).''','''* `unaryTokenTM` (`unaryTokenTM_computes`), `appendBitTM` (`appendBitTM_computes`);
* `pairMapSndTM` (`pairMapSndTM_computes`, `pairMapSndTM_spaceUsed`), the forwarding
  mapper with time coefficient `22` and coefficient one on the payload's space.''','Index all three new forwarding exports and their frozen coefficients.')
replace(f,'''`polyUnaryTM_spaceUsed`, `unaryTokenTM_computes` and `appendBitTM_computes` are sorried
until the fill F-B; every other spec has a proof, and the ones that cite a spec sorried until
its own fill depend on it (`polyBitsTM_computes`, `stripLastTM_computes` and the three
split-search specs).''','''Every named specification is proved. The polynomial-bit, stripping and split-search
results consume the corresponding named time and space specifications.''','Retire the now-false three-admission status paragraph.')
sketches={
'fwdMap_block':"Apply the first aligned parser step, then inspect the second bit. Equal bits append one bit to the first buffer; `01` begins suffix copying and `10` halts. The published action fields and buffer-append equation identify the complete configuration in each case.",
'fwdMap_suffix':"Induct on the unread suffix. A present bit appends to the second buffer and advances its head and the native input once; the empty suffix reads the right blank and starts its rewind. The first buffer and payload bank remain unchanged throughout.",
'fwdMap_backB':"Induct on the remaining second-buffer head distance. Each nonblank position makes one left move without changing a tape. At position `-1` the blank-reading transition moves right to zero and enters the first-buffer rewind phase.",
'fwdMap_backA':"Induct on the remaining first-buffer head distance. Each nonblank position makes one left move without changing a tape. At position `-1` the blank-reading transition moves right to zero and enters the first-buffer emission phase.",
'fwdMap_finish':"Compose suffix copying, the two buffer rewinds, and emission of the first component and delimiter. Their time sum is `3 * |a| + 2 * |b| + 5`. The initialization field equations identify the endpoint with the payload machine's virtual initial configuration on `b`.",
'fwdMap_setup':"Specialize the parser theorem to the complete input with empty consumed prefix and empty buffers. The public initialization fields identify the machine's genuine start configuration with that parser configuration. Its successful virtual launch and unsuccessful silent halt give the two decoder cases with the same linear budget.",
'fwdMapVirtual_step':"A halted source remains fixed. For a live source, the virtual-move contract supplies the next boundary tag and buffered input-head position. The action field equations then identify the preserved first buffer, virtual input buffer, payload bank, fixed physical input head, and forwarded output prefix.",
'fwdMapSetup_head_step':"Inspect the setup controller's phases and the possible pending bit and read symbol. Every setup action leaves the payload-bank heads stationary, including the absorbing setup view of the run phase. The public step and action head equations transfer that table fact to the complete step.",
'fwdMap_launch':"Choose the first time the absorbing setup view enters a virtual payload state. Guarded setup agreement identifies every real prefix through that time. Absorption identifies this first-entry configuration with the already bounded final setup configuration, retaining the same linear bound.",
'fwdMap_reject':"The bounded setup run halts silently. A virtual payload state cannot occur before this halt, since that state is absorbing in the setup view, or afterward, since a halted run remains fixed. The two controllers therefore agree for every prefix and have the same bounded silent rejection."}
old=R.STAGES['current'][f]
for short,text in sketches.items():
 d=next(d for d in R.DECLS['current'][f] if d['name']=='Turing.FinTM.'+short);doc=d['doc'];assert doc and '**Proof sketch.**' not in doc;protected=re.sub(r'`[^`]*`',lambda m:m[0].replace(' ','\x00'), '**Proof sketch.** '+text);paragraph=textwrap.fill(protected,width=97,break_long_words=False,break_on_hyphens=False).replace('\x00',' ');new=doc.removesuffix('-/').rstrip()+'\n\n'+paragraph+' -/'
 replace(f,doc,new,'Add the leading sketch for the '+short+' proof (>20 lines).')
f='TCSlib/Complexity/TuringMachine/Build/Loop.lean'
a=R.STAGES['current'][f];start=a.index('**Fill checkpoint (batch L).**');end=a.index('\n-/',start)
replace(f,a[start:end],'''The concrete controller assembles the completed fuel, startup, body-return,
counter and payload phases in `loopHost_contracts`, with uniform coefficient
`loopHost_bound = 10`. Canonical seams retain the fuel residue and fixed-width
debit iterates. Underflow and its final emission belong to the last rejecting
segment; an accepting last candidate has an arbitrary unreachable rejection
terminal. The capture helpers consume the proved `capture_run` contract.''','Replace historical unproved/proved checkpoint prose with the current mathematical construction.')
replace(f,"/-- The audit's single maximum: startup coefficient nine, body coefficient","/-- The controller's uniform maximum: startup coefficient nine, body coefficient",'Describe the numeric ledger without an audit label.')
replace(f,"the audit's maximum\nledger.","the controller's maximum\nledger.",'Describe the completed controller ledger without an audit label.')
replace(f,'''**Continuation frontier: unproved.** The public corollaries below are conditional
on this one machine-construction obligation; this is not a closed batch.

''','', 'Remove the obsolete private-contract frontier status.')
replace(f,'''ledger. The missing proof is precisely the controller-level lifting and
assembly of these phase contracts, including startup and replay bounds.''','''ledger. This assembles the controller-level phase contracts, including the
startup and replay bounds.''','Make the proof sketch describe the completed assembly.')
replace(f,'''/- Batch L2 closure: the preceding continuation docstring is retained as
historical evidence. Its listed obligations are discharged below by the phase
lemmas and the canonical family; there is no remaining construction admission. -/
''','', 'The current proof sketch no longer needs a historical correction block.')
patch='';manifest=[]
for f,new in proposed.items():
 old=R.STAGES['current'][f];assert R.P.norm(R.P.clean(old))==R.P.norm(R.P.clean(new)),f
 q=out/'proposals/source-comments'/(f+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(new)
 patch+=''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='a/'+f,tofile='b/'+f))
 manifest.append({'path':f,'frozen_source_sha256':R.H(old),'proposed_comment_source_sha256':R.H(new),'noncomment_tokens_identical':True})
(out/'proposed-source-comments.patch').write_text(patch)
# Two registry pointers are changed only after the retirement actually merges. Historical backlog rulings remain intact.
registry=root/'machine-library-design.md';old=registry.read_text();new=old
x='''stated generically from the start, and the canonical `compareTM_run` is
  re-derived from it by a sanctioned body swap, exactly as §12.6 did for
  copy/transfer/clear.''';y='''stated generically through `compareTM_run_ofCfg`. Canonical configurations
  use that framed contract; the old canonical-only specialization is retired
  together with the other canonical catalog rows.''';assert new.count(x)==1;new=new.replace(x,y)
x='''Canonical `compareTM_run` re-derived (body swap); the trace generalizes `catalog_compare_trace`''';y='''Canonical seams use the framed contract; the trace generalizes `catalog_compare_trace`''';assert new.count(x)==1;new=new.replace(x,y)
(out/'proposed-postmerge-registry.patch').write_text(''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='a/machine-library-design.md',tofile='b/machine-library-design.md')))
(out/'proposals/machine-library-design.md').write_text(new)
(out/'comment-proposals.json').write_text(json.dumps({'applied':False,'source_files':manifest,'source_comment_changes':edits,'ten_sketches':list(sketches),'postmerge_registry':{'path':'machine-library-design.md','base_sha256':R.H(old),'proposed_sha256':R.H(new),'pointer_changes':2,'apply_only_after_retirement_merge':True},'backlog_retirement_hit':'Historical answered conditional/ruling, intentionally retained. No merge/status claim is pre-written.'},indent=2)+'\n')
print(json.dumps({'source_comment_files':len(proposed),'comment_changes':len(edits),'sketches':len(sketches),'source_noncomment_tokens_unchanged':True,'postmerge_registry_pointers':2,'actual_source_modified':False},indent=2))
