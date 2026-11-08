"""Optional source-only sketch synchronization after the body proposal; no live source writes."""
from pathlib import Path
import difflib,hashlib,json,textwrap
p=Path(__file__).resolve().parent
H=lambda s:hashlib.sha256(s.encode()).hexdigest()
forward='Apply `Turing.MultiTapeTM.exists_first_entry_of_fixed` to the same stop predicate and complete absorbing-configuration hypothesis. The public contract supplies the first-entry cut and the exact bounded endpoint.'
texts={
('Loop','emCall_first_entry'):forward,
('Primitives','emitter_first_entry'):forward,
('Primitives','catalogFirstEntry'):'Specialize `Turing.MultiTapeTM.exists_first_entry_of_fixed` to equality with the selected control state, then project its predicate cut to the required singleton-state cut.',
('Loop','emCall_eval_first'):'Use `Turing.MultiTapeTM.exists_first_halt` for the first source halt and complete configuration equality with the supplied deadline. This equality transports the specified output unchanged. Apply captured virtual lockstep through that halt and every earlier prefix; the deadline supplies only an inequality, never a native clock.',
('Loop','emCall_right_endpoint'):'Use `Turing.MultiTapeTM.exists_first_halt` to retain the completed source configuration and strict earlier-time liveness. The native right scan then costs at most `|x|+2`; absorb only that completed run to the advertised budget. The public complete endpoint equality retains the work tapes at the original deadline.',
('Primitives','lenStart'):'Use `Turing.MultiTapeTM.exists_first_halt` to supply the strict liveness guard to `Turing.capture_run` and to transport the specified output through complete configuration equality. One native step moves the capture head left; quantitative rewind restores the input head while preserving the completed generator bank.',
('Primitives','splitBody_count'):'Apply `Turing.MultiTapeTM.exists_first_halt` to the arbitrary source bank, then compose its complete endpoint equality with the supplied counted-run endpoint. Apply the counted correspondence to every prefix through that halt; its control image is disjoint from the anchor, including the return state.',
('Wrappers','timed_start'):'Use `Turing.MultiTapeTM.exists_first_halt` for the first source halt within budget and its exact completed singleton output. Capture until that halt, read the singleton in two steps, and rewind in at most the current input position plus two. Charge this rewind to the decider\'s elapsed steps using the head-position bound.',
('Composition','condTM_start'):'Use `Turing.MultiTapeTM.exists_first_halt` for the strict source liveness cut and complete configuration equality with the given deadline. Transport the completed output `[b]` along that equality, then apply controller lockstep and rewind. The branch tapes and physical output stay untouched.',
('Simulation','bufferedComp_start'):'Use `Turing.MultiTapeTM.exists_first_halt` for the first halt by `t₁` and transport the complete output `y` from the deadline. First-phase lockstep reaches that completed configuration; the exact rewind lemma supplies `|y| + 2` more steps while retaining the first block and parked native input head.',
('Primitives','splitEmbed_cut'):'Use `Turing.MultiTapeTM.exists_first_entry_of_fixed` with the supplied stop predicate, fixed-step hypothesis and complete endpoint. Induct on the host prefix using transition agreement only before the returned strict cut; every mapped control state, including a halted state, stays away from the host anchor.',
('Primitives','fwdMap_launch'):'The existing stationary-setup contract at one step proves that every virtual-payload stop configuration is fixed. Apply `Turing.MultiTapeTM.exists_first_entry_of_fixed` to that stop predicate and the bounded setup endpoint. Guarded setup agreement then identifies every operational prefix through the returned first entry, with the same complete endpoint and linear bound.',
('Catalog','computesFunInTime_pairDup_spaceUsed'):'Retain the witness `Turing.pairDiagTM` and the time coefficient from `Turing.pairDiagTM_computes`. The published `Turing.pairDiagTM_spaceUsed` gives zero space directly, so the existing constant-space witness bounds it.',
('Catalog','computesFunInTime_incFixed_spaceUsed'):'Retain the existing witness `Turing.FinTM.incFixedTM` and its time coefficient. The published `Turing.FinTM.incFixedTM_spaceUsed` gives zero space directly, so the existing constant-space witness bounds it.'}
original={};current={}
for owner,name in texts:
 if owner not in current:
  original[owner]=current[owner]=(p/'inputs'/f'{owner}-after15-b1-REQUIRES-INTEGRATED-API119.lean.txt').read_text()
 s=current[owner];a=s.index('lemma '+name) if 'lemma '+name in s else s.index('theorem '+name)
 start=s.rfind('/--',0,a);end=s.index('-/',start)+2;assert end<a
 doc=s[start:end];marker=doc.index('**Proof sketch.**')
 newdoc=doc[:marker]+textwrap.fill('**Proof sketch.** '+texts[(owner,name)],width=98,break_long_words=False,break_on_hyphens=False)+' -/'
 current[owner]=s[:start]+newdoc+s[end:]
old='`Turing.FinTM.redirectTM_spaceUsedByTape` (W2),'
new='`Turing.FinTM.redirectTM_spaceUsedByTape` (W2, imported from `Build/Wrappers`),'
assert current['Catalog'].count(old)==1;current['Catalog']=current['Catalog'].replace(old,new,1)
patch='';rows=[]
for owner in original:
 path='TCSlib/Complexity/TuringMachine/'+('Build/' if owner in ['Loop','Primitives','Catalog','Wrappers'] else '')+owner+'.lean'
 patch+=''.join(difflib.unified_diff(original[owner].splitlines(keepends=True),current[owner].splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path))
 (p/'inputs'/f'{owner}-after15-body-and-sketch-b1-REQUIRES-INTEGRATED-API119.lean.txt').write_text(current[owner])
 rows.append({'file':path,'body_only_sha256':H(original[owner]),'with_optional_sketches_sha256':H(current[owner])})
(p/'optional-sketches-after-bodies.patch').write_text(patch)
(p/'optional-sketches.json').write_text(json.dumps({'scope':'Comment-only optional patch against generation2 body-proposal outputs; preserve proof semantics/headers. No actual source edit.','proof_sketches':14,'owner_index_lines':1,'files':rows},indent=2)+'\n')
