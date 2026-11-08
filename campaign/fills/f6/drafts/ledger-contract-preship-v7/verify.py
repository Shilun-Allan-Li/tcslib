from pathlib import Path
import hashlib,json,re
out=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((out/'context.json').read_text())
s=(out/'Final-sealed.lean.txt').read_text()
guard=(out/'guard.txt').read_text()
assert s.replace(guard,'')==(out/'Final-native.lean.txt').read_text()
proof=s.split('namespace F6LedgerPreship',1)[1].split('end F6LedgerPreship',1)[0]
assert not re.search(r'\b(sorry|admit|unsafe|axiom|unfold)\b',proof)
guards=set((out/'control-definitions.txt').read_text().splitlines())
first=s[:s.index('namespace F6LedgerPreship')].count('\n')+1
last=s[:s.index('end F6LedgerPreship')].count('\n')+1
rows=[{'line':i,'text':l.strip()} for i,l in enumerate(s.splitlines(),1)
      if first<=i<last and re.search(r'\b(?:simpa|simp|dsimp|rw)\b',l)]
for row in rows:
 for n in guards:
  assert not re.search(r'(?<![A-Za-z0-9_.])'+re.escape(n)+r'(?![A-Za-z0-9_.])',row['text'])
named=[{'line':i,'text':l.strip()} for i,l in enumerate(s.splitlines(),1) if re.search(r'\b\w+\s*:=',l)]
scan={'no_sorry_admit_unsafe_axiom_unfold_in_four_roots':True,'guard_removal_exact_byte_identity':True,'guard_before_first_header':s.index(guard)<s.index('/--'),'explicit_simp_dsimp_rw_rows':rows,'named_argument_rows':named,'manual_named_argument_disposition':'The bundle constructor has only k:=1, State:=Fin(M.numStates+1), tm:=M.tm; these are projections of the published bundle RHS. No foreign definition is passed to simplifier/unfold tactics. Instrumentation reads compiled constants separately from the four proof roots.'}
(out/'source-scan.json').write_text(json.dumps(scan,indent=2)+'\n')
m=json.loads((out/'metadata.json').read_text())
assert len(m['roots'])==4 and len(m['root_and_descendant_axioms'])==20
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in m['root_and_descendant_axioms'])
assert set(m['direct_ordinary_definitions'])<=guards
checks=json.loads((out/'control-check.json').read_text());assert checks['all_exact_multiplicities_match']
attempts=[]
for p in sorted(out.glob('*-run.json')):
 r=json.loads(p.read_text());log=out/(p.name.removesuffix('-run.json')+'.out')
 r['warnings']=len(re.findall(r'^.*:\d+:\d+: warning:',log.read_text(),re.M))
 attempts.append({'name':p.name.removesuffix('-run.json'),**{k:r[k] for k in ['exit','errors','warnings','seconds','input_sha256','output_sha256']}})
for name in ['Final-native','Final-sealed']:
 r=next(x for x in attempts if x['name']==name);assert (r['exit'],r['errors'],r['warnings'])==(0,0,0)
unchanged={}
for p,h in c['sources'].items():unchanged[str(Path(c['worktree'])/p)]=sha(Path(c['worktree'])/p)==h
for p,h in c['compiled'].items():unchanged[str(Path(c['snapshot'])/p.replace('.lean','.olean'))]=sha(Path(c['snapshot'])/p.replace('.lean','.olean'))==h
assert all(unchanged.values())
(out/'pin-recheck.json').write_text(json.dumps(unchanged,indent=2)+'\n')
v={'status':'PASS bounded conditional types/arithmetic only; no actual prefix/ledger/target/dispatch acceptance','attempts':attempts,'four_root_count':4,'compiled_descendant_count':16,'all_twenty_selected_standard_axioms':True,'guard_definitions':len(guards),'direct_TCSlib_ordinary_definitions':len(m['direct_ordinary_definitions']),'direct_ordinary_all_guarded':True,'controls_pairs':checks['pointwise_and_abstracted_pairs'],'controls_all_exact':True,'source_and_snapshot_pins_unchanged':True,'native_sealed_guard_removal_byte_identity':True,'firsthalt_and_output_are_OWN_hypotheses_not_proved':True,'actual_prefix_per_code_constants_are_OWN_not_derived':True,'actual_hosted_tape_ledger_NOT_constructed':True,'source_git_snapshot_cache_screen_admission_changes':False}
(out/'verification.json').write_text(json.dumps(v,indent=2)+'\n')
print(json.dumps({k:v[k] for k in ['four_root_count','compiled_descendant_count','guard_definitions','direct_TCSlib_ordinary_definitions','controls_pairs']},indent=2))
