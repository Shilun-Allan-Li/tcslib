from pathlib import Path
import collections,hashlib,json,re
p=Path(__file__).resolve().parent;root=p.parents[4];H=lambda b:hashlib.sha256(b).hexdigest();g=(p/'guard.txt').read_text();guarddefs=g.splitlines()[0].split('] ',1)[1].split()
assert len(guarddefs)==32 and len(set(guarddefs))==32
assert (p/'SourceHalt-sealed.lean.txt').read_text().replace(g+'\n','',1)==(p/'SourceHalt-native.lean.txt').read_text()
assert (p/'Controls-sealed.lean.txt').read_text().replace(g,'',1)==(p/'Controls-unsealed.lean.txt').read_text()
for n in ['SourceHalt-native','SourceHalt-sealed','Controls-unsealed','Controls-sealed']:
 r=json.loads((p/(n+'-run.json')).read_text());assert r['input_stable'] and H((p/(n+'.out')).read_bytes())==r['output_sha256'];assert r['exit']==(1 if n=='Controls-sealed' else 0) and r['errors']==(64 if n=='Controls-sealed' else 0) and r['warnings']==0
idx=json.loads((root/'campaign/fills/f6/drafts/layout-preship-v2/controls-index.json').read_text());assert {x['definition'] for x in idx}==set(guarddefs);(p/'controls-index.json').write_text(json.dumps(idx,indent=2)+'\n')
diags=[(int(m[1]),m[2]) for m in re.finditer(r'(?m)^.*\.lean:(\d+):\d+: error(?:\([^)]*\))?: ([^\n]*)',(p/'Controls-sealed.out').read_text())];expected=[(x[k],'Tactic `rfl` failed: The left-hand side') for x in idx for k in ['pointwise_error_line','abstracted_error_line']]
assert collections.Counter(diags)==collections.Counter(expected);synthetic=[diags[0]]+diags[:-1];assert len(synthetic)==64 and collections.Counter(synthetic)!=collections.Counter(expected)
meta=(p/'SourceHalt-sealed.out').read_text();ordinary=[];abbrev=[];ax=[]
for l in meta.splitlines():
 if l.startswith('AX|'):
  _,n,vals=l.split('|');a=vals.strip('[]').split(', ');assert set(a)<={'propext','Classical.choice','Quot.sound'};ax.append({'name':n,'axioms':a})
 if l.startswith('DEF|'):
  _,n,d,home,h=l.split('|');row={'root':n,'definition':d,'home':home,'hints':h};(abbrev if h=='abbrev' else ordinary).append(row)
assert len(ax)==1 and all(x['definition'] in guarddefs for x in ordinary)
summary={'scope':'One conditional CodeTM first-halt/arbitrary-output/configuration-equality bridge, no F6 target/prefix/loop proof','proof_base':'3023dc1408c3d216fc07a7cbba9ae30135b861ed','snapshot':'oleans-mac4','native_and_sealed_exit_errors_warnings':[0,0,0],'guard_before_doc_complete_header_and_body':True,'guard_definitions':32,'default_simp_removals':3,'ordinary_foreign_definitions':ordinary,'structure_projection_and_Halted_abbrev_exclusions':abbrev,'roots_and_descendants':ax,'fresh_unsealed_controls':64,'fresh_sealed_exact_expected_rfl_failures':64,'controls_one_per_recorded_definition_mode_and_identity':True,'same_count_duplicate_drop_perturbation_rejected':True,'explicit_arguments':['CodeTM.toFinTM_eq: published constructor reader','FinTM.computesInTime_iff: published computation reader','MultiTapeTM.exists_first_halt: published first-halt bridge','he: local complete configuration equality'],'no_named_foreign_definition_unfold_argument':True,'no_actual_source_snapshot_Git_cache_or_screen_mutation':True}
(p/'verification.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({'ordinary_foreign_defs':len(ordinary),'abbrev_exclusions':len(abbrev),'roots':len(ax),'controls':64,'pass':True},indent=2))
