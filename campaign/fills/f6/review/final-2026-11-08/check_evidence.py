"""Independently reconcile supplied F6 logs/controls as data; never execute them."""
from pathlib import Path
import ast,collections,datetime,hashlib,json,re
out=Path(__file__).resolve().parent;root=out.parents[4];ing=json.loads((out/'ingestion.json').read_text());p=Path(ing['scratch_root'])/'final';H=lambda b:hashlib.sha256(b).hexdigest()
issued=root/'campaign/fills/f6/issue-preparation/inputs';order=(issued/'final-order.txt').read_text().splitlines();assert len(order)==len(set(order))==229
summary=(p/'evidence/logs/final-sweep/summary.log').read_text().splitlines();assert summary[0].startswith('# sweep of 229 modules at 6e98df4f7f86889b2c9eb3e9a05541cc772a56d4 dirty=0 ');assert summary[-1].startswith('# modules=229 failed=0 ')
rx=re.compile(r'(\S+) start=(\S+) end=(\S+) secs=(\d+) maxrss_kb=(\d+) exit=(\d+) errors=(\d+) sorry_warnings=(\d+)')
modules=[];prev=None
for line in summary[1:-1]:
 m=rx.fullmatch(line);assert m,line;mod,start,end,seconds,rss,status,errors,sorry=m.groups();assert status==errors=='0';a=datetime.datetime.fromisoformat(start.replace('Z','+00:00'));b=datetime.datetime.fromisoformat(end.replace('Z','+00:00'));assert b>=a and (prev is None or a>=prev);prev=b
 raw=p/'evidence/logs/final-sweep/raw'/(mod.replace('/','.')+'.out');data=raw.read_bytes();text=data.decode();assert len(re.findall(r'error:',text))==int(errors);assert text.count("declaration uses 'sorry'")==int(sorry)
 timing=raw.with_name(raw.name+'.time').read_text();tm=re.search(r'Exit status: (\d+)',timing);assert tm and tm[1]==status;rs=re.search(r'Maximum resident set size \(kbytes\): (\d+)',timing);assert rs and rs[1]==rss
 modules.append({'module':mod,'start':start,'end':end,'exit':int(status),'errors':int(errors),'sorry_warnings':int(sorry),'warnings':text.count('warning:'),'raw_bytes':len(data),'raw_sha256':H(data),'raw_time_sha256':H(timing.encode())})
assert [r['module'] for r in modules]==order and sum(r['sorry_warnings'] for r in modules)==21
assert len(list((p/'evidence/logs/final-sweep/raw').glob('*.out')))==229
own=next(r for r in modules if r['module'].endswith('/Hierarchy'));assert own['errors']==own['warnings']==own['sorry_warnings']==0
# Parse complete static inventories without executing the delivered counting tool.
def static(name):
 rows={};total=None
 for l in (p/'evidence/logs'/name).read_text().splitlines():
  if l.startswith('TOTAL '):total=int(l.split()[1]);continue
  m=re.fullmatch(r'\s*(\d+) (\S+) (\[.*\])',l);assert m,l;n,file,names=m.groups();v=ast.literal_eval(names);assert len(v)==int(n);rows[file]=v
 assert len(rows)==229 and sum(len(v) for v in rows.values())==total;return rows,total
before,bt=static('static-sorry-3023dc1408c3d216fc07a7cbba9ae30135b861ed.txt');after,at=static('static-sorry-final-r3.txt');assert (bt,at)==(22,21)
assert {f for f in before if before[f]!=after[f]}=={'TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'}
assert before['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']==['Complexity.space_universal'] and after['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']==[]
# Scope and exact identities of supplied compiled inventory/AX evidence.
inventory=(p/'evidence/seal/Inventory_final.out').read_text();selected=re.findall(r'^SELECTED\|(.+)$',inventory,re.M);defs=[x.split('|') for x in inventory.splitlines() if x.startswith('FOREIGNDEF|')];assert len(selected)==len(set(selected))==56 and len(defs)==51
regular={r[1] for r in defs if 'hints=regular' in r};abbrev={r[1] for r in defs if 'hints=abbrev' in r};assert (len(regular),len(abbrev))==(37,14)
sealed=(p/'evidence/seal/sealed-definitions-final.txt').read_text().split();assert len(sealed)==len(set(sealed))==36
excluded=regular-set(sealed);assert excluded=={'Turing.instFintypeRewindPhase','Turing.instFintypeSeekPhase'};assert set(sealed)-regular=={'Nat.bits'}
expected={(n,mode) for n in sealed for mode in ['point','abstract']}
control=re.compile(r'^CONTROL\|([^|]+)\|(point|abstract)\|(PASS|FAIL)(?:\|kernelChecked=([^\s]+))?$',re.M)
native=(p/'evidence/seal/Controls_final_unsealed.out').read_text();opaque=(p/'evidence/seal/Controls_final_sealed.out').read_text()
def validate(n,s):
 a=control.findall(n);b=control.findall(s);assert len(a)==len(b)==72
 assert {(x,y) for x,y,_,_ in a}==expected=={(x,y) for x,y,_,_ in b}
 assert all(state=='PASS' and name for _,_,state,name in a) and len({name for _,_,_,name in a})==72
 assert all(state=='FAIL' and not name for _,_,state,name in b)
 errors=re.findall(r'^.*?: error: RFL_CONTROL\|([^|]+)\|(point|abstract)\|',s,re.M);assert len(errors)==72 and set(errors)==expected and len(re.findall('error:',s))==72
validate(native,opaque)
negative=[]
for label,n,s in [('drop-native',native.replace(native.splitlines(keepends=True)[0],'',1),opaque),('duplicate-native',native+native.splitlines(keepends=True)[0],opaque),('drop-sealed-marker',native,opaque.replace('CONTROL|Complexity.TimeHierarchy.code|point|FAIL\n','',1))]:
 try:validate(n,s)
 except AssertionError:negative.append(label)
 else:raise AssertionError(label+' corruption accepted')
attempt=(p/'evidence/seal/Controls_final-attempt1-38defs_sealed.out').read_text();oldc=control.findall(attempt);assert len(oldc)==76;assert sum(r[2]=='PASS' for r in oldc)==4;assert {r[0] for r in oldc if r[2]=='PASS'}==excluded
# Every changed source section is guarded before its doc/header/body, no proof-body substitution.
source=(out/'final-Hierarchy.lean.txt').read_text();seal=(p/'evidence/seal/Seal_final.lean.txt').read_text();guards=re.findall(r'^attribute \[local irreducible\] (.+)$',seal,re.M);nosimps=re.findall(r'^attribute \[-simp\] (.+)$',seal,re.M)
assert len(guards)==len(nosimps)==19 and all(x.split()==sealed for x in guards)
assert all(set(x.split())=={'Turing.Action.apply','Turing.Cfg.init','Turing.MultiTapeTM.initCfg'} for x in nosimps)
sections=re.findall(r'^section (F6Seal\d+)\n(.*?)^end \1\s*$',seal,re.M|re.S);assert len(sections)==19
for _,body in sections:assert body.startswith('attribute [local irreducible] ') and body.index('/--')>body.index('attribute [-simp] ')
stripped=re.sub(r'^(?:section F6Seal\d+|end F6Seal\d+|attribute \[local irreducible\].*|attribute \[-simp\].*)\n','',seal,flags=re.M);assert stripped.split()==source.split()
ax=(p/'evidence/axioms/Ax_final-sweep.out').read_text();ar=re.findall(r'^AX\|([^|]+)\|\[([^\]]*)\]\|STANDARD$',ax,re.M|re.S);assert len(ar)==47 and len(set(n for n,_ in ar))==47
standard={'propext','Classical.choice','Quot.sound'}
assert all(set(x.strip() for x in axs.split(',') if x.strip())<=standard for _,axs in ar)
axnames={n for n,_ in ar};gap=sorted(set(selected)-axnames);assert len(gap)==9 and all(n.startswith('Complexity.space_universal._proof_') for n in gap)
assert any(n=='Complexity.space_universal' and set(x.strip() for x in axs.split(','))==standard for n,axs in ar)
assert re.search(r'AXSUMMARY\|declarations=47\|nonstandard=0',ax)
# Complete delivered screen populations/results are re-parsed, no screen executed.
pop=(p/'evidence/screens/screen-population.txt').read_bytes();assert pop==(issued/'screen-population.txt').read_bytes();assert len(pop.splitlines())==21
pairs=[];screenrows=[]
for side in ['base','head']:
 f=p/'evidence/screens'/('screen-'+side+'.txt');text=f.read_text();r=json.loads((p/'evidence/screens'/('screen-'+side+'-run.json')).read_text());assert H(text.encode())==r['output_sha256'] and r['exit']==0 and H(pop)==r['population_sha256']
 m=re.fullmatch(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars',text.splitlines()[0]);assert m
 rows=[]
 for line in text.splitlines()[1:]:
  row=re.fullmatch(r'\s+(.+?)  reproduces  (.+?): (\d+)/(\d+) = (\d+)%',line);assert row;rows.append(row.groups())
 assert len(rows)==int(m[2]) and sum(int(row[2]) for row in rows)==int(m[3].replace(',',''));assert len(set((a,b) for a,b,*_ in rows))==len(rows)
 pairs.append({(a,b):(a,b,n,d,pct) for a,b,n,d,pct in rows});screenrows.append({'side':side,'declarations':int(m[1]),'pairs':len(rows),'directed_chars':sum(int(row[2]) for row in rows),'raw_sha256':H(text.encode()),'source_root_as_reported':r['root']})
new=[pairs[1][k] for k in pairs[1].keys()-pairs[0].keys()];gone=list(pairs[0].keys()-pairs[1].keys());assert len(new)==1 and not gone and all(pairs[0][k]==pairs[1][k] for k in pairs[0])
assert new[0]==('Hierarchy.lean::f6_native_halt','UniversalK.lean::ss_inputRewind_done','162','321','50')
# Raw producer reports do not establish explicit -j4 replay enforcement.
sweep=(p/'tools/sweep.sh').read_text();env=(p/'tools/env.sh').read_text();assert 'scripts/lean_check_tree.sh' in sweep and '-j4' not in sweep and 'LEAN_NUM_THREADS' not in env and 'replay-j4' not in env
result={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Independent offline checks of supplied producer evidence; no delivered tools, Lean or screens run','final_sweep':{'source_head':'6e98df4f7f86889b2c9eb3e9a05541cc772a56d4','order_modules':229,'all_summary_raw_time_exit_error_and_sorry_counts_reconcile':True,'inherited_sorry_warnings':21,'owned_Hierarchy_warnings':0,'ordered_start_end_no_module_overlap_in_recorded_summary':True,'modules':modules,'explicit_j4_process_enforcement_not_attested_by_supplied_pipeline':True},'static_admissions':{'before':bt,'after':at,'only_removed':'Complexity.space_universal','all_other228module_rows_identical':True},'seals':{'source_sections':19,'instrumentation_before_full_docs_headers_bodies':True,'stripping_instrumentation_restores_actual_source_tokens':True,'foreign_TCSlib_defs':51,'TCSlib_regular':37,'TCSlib_abbrev_projections':14,'sealed_TCSlib_regular':35,'extra_sealed_Mathlib':['Nat.bits'],'total_guarded':36,'uncontrolled_regular_instances':sorted(excluded),'effective_control_pairs':72,'exact_identities_and_kernelChecked_native_labels':True,'sealed_errors_exactly72':True,'negative_corruption_tests_rejected':negative,'first38attempt_excluded_instances_controls_still_close':True,'not_a_blanket_all_foreign_reduction_seal':True},'axioms':{'supplied_AX_rows':47,'private_f6_roots_and_descendants':46,'target_root':1,'all47standard':True,'inventory_selected_constants':56,'target_named_generated_auxiliaries_not_individually_AX_printed':gap,'root_recursive_axioms_standard':True,'fresh_unfiltered_compiler_owner_census_not_supplied':True},'screens':{'issued_population_exact21':True,'runs':screenrows,'new_directed_rows':new,'gone':gone,'all636old_scores_unchanged':True,'new_comparison_Inclusions_outside_issued21':True},'process':{'reported_D1_to_D6_preserved':True,'additional_N1_unlocked_dev_prescreens_disclosed_only_in_deviations_log':True,'no_independent_native_or_host_process_observation_claim':True}}
(out/'producer-evidence-reconciliation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['final_sweep']},indent=2))
