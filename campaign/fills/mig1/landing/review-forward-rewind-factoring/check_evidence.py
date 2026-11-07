"""Check bounded native/seal/control receipts and literal reconstruction; no Lean or source writes."""
from pathlib import Path
import hashlib,json,re
out=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b.encode() if isinstance(b,str) else b).hexdigest()
source=(out/'candidate-Primitives.lean.txt').read_text();before=(out/'before-Primitives.lean.txt').read_text();m=json.loads((out/'seal-v2-manifest.json').read_text())
native=json.loads((out/'Candidate-native-v1-run.json').read_text());sealed=json.loads((out/'Candidate-sealed-v2-run.json').read_text());assert native['exit']==0 and native['errors']==0;assert sealed['exit']==0 and sealed['errors']==0
for stem in ['Helper-prefix-v1','Candidate-native-v1','Candidate-sealed-v1','Candidate-sealed-v2','Controls37-unsealed-v1','Controls37-sealed-v1']:
    r=json.loads((out/(stem+'-run.json')).read_text());assert r['input_sha256']==H((out/(stem+'.lean.txt')).read_bytes()) and r['output_sha256']==H((out/(stem+'.out')).read_bytes())
raw=(out/'Candidate-native-v1.out').read_text();roots=re.findall(r'^ROOT\|([^|]+)\|private=(\w+)\|simp=(\w+)\|unfold=(\w+)$',raw,re.M);assert len(roots)==3 and all(x[1:]==('true','false','false') for x in roots)
ax=re.findall(r'^AXIOMS\|([^|]+)\|\[(.*?)\]$',raw,re.M);assert len(ax)==6 and len({n for n,_ in ax})==6
assert all(set(a.split(', '))<={'propext','Classical.choice','Quot.sound'} for _,a in ax)
sealed_ax=re.findall(r'^AXIOMS\|([^|]+)\|\[(.*?)\]$',(out/'Candidate-sealed-v2.out').read_text(),re.M);assert sorted(sealed_ax)==sorted(ax)
defs=[dict(zip(['root','name','owner','hint'],r)) for r in re.findall(r'^DEF\|([^|]+)\|([^|]+)\|([^|]+)\|hint=(\w+)$',raw,re.M)]
ordinary={d['name'] for d in defs if d['hint']!='abbrev'};abbrevs={d['name'] for d in defs if d['hint']=='abbrev'};assert ordinary<=set(m['definitions'])
# The new proof's explicit rules were inspected individually, not accepted based on seal success alone.
explicit=[]
for line in (out/'helper-v1.lean.txt').read_text().splitlines():
    if 'simp' in line or 'rw [' in line:explicit.append(line.strip())
argument_result={'new_helper_and_two_consumers_only':True,'ordinary_foreign_definition_arguments':[],'forbidden_named_Core_Mathlib_def_arguments':[],'allowed_same_home_definition_arguments':['fwdMapTM','fwdMapCfg'],'equation_readers':['MultiTapeTM.runFrom_succ_eq_step','MultiTapeTM.runFrom_zero','MultiTapeTM.step_of_some','Cfg.workTapeSymbols_eq','tapeBlocks_left','tapeBlocks_buffer','bufferTape_left','bufferTape_nat','fwdMap_move'],'math_or_simplifier_theorems':['Bool.false_eq_true','↓reduceIte','Nat.cast_zero','zero_sub','List.getElem?_eq_getElem','sub_eq_add_neg'],'reviewed_head_lines':explicit,'scope':'Manual inspection of all complete bracket lists in helper and two consumer bodies; no argument-name inference from grep alone.'}
# Exact controls from the existing reviewed template, freshly calibrated in current complete context.
us=(out/'Controls37-unsealed-v1.lean.txt').read_text();ss=(out/'Controls37-sealed-v1.lean.txt').read_text();assert set(re.search(r'^attribute \[local irreducible\] (.*)$',ss,re.M)[1].split())==set(m['definitions']);assert us==(out.parent/'review-primitives/Controls-37-unsealed-v1.lean.txt').read_text()
starts=[];pair=None;form=0
for i,l in enumerate(ss.splitlines(),1):
    x=re.match(r'-- (C\d\d)\b',l)
    if x:pair=x[1];form=0
    if l.startswith('example'):
        form+=1;assert pair and form<=2;starts.append({'pair':pair,'form':form,'line':i})
assert len(starts)==74 and len({r['pair'] for r in starts})==37
ends=[r['line'] for r in starts[1:]]+[len(ss.splitlines())+1]
def parse(t):return [{'line':int(x[1]),'col':int(x[2]),'message':x[3]} for x in re.finditer(r'^.*?:(\d+):(\d+): error(?:\([^)]*\))?: (.*)$',t,re.M)]
def check(ds):
    assert len(ds)==74,('total',len(ds))
    rows=[];used=[]
    for start,end in zip(starts,ends):
        hits=[(i,d) for i,d in enumerate(ds) if start['line']<=d['line']<end]
        assert len(hits)==1,('multiplicity',start,len(hits));i,d=hits[0];assert 'rfl' in d['message'];used.append(i);rows.append(dict(start,diagnostic=d))
    assert sorted(used)==list(range(74));return rows
ds=parse((out/'Controls37-sealed-v1.out').read_text());coverage=check(ds)
try:check([ds[0],ds[0]]+ds[2:])
except AssertionError as e:negative={'rejected':True,'same_total':True,'reason':repr(e.args)}
else:raise AssertionError('duplicate/drop control accepted')
ur=json.loads((out/'Controls37-unsealed-v1-run.json').read_text());sr=json.loads((out/'Controls37-sealed-v1-run.json').read_text());assert ur['exit']==0 and ur['errors']==0;assert sr['exit']==1 and sr['errors']==74
controls={'fresh_context_execution':True,'reviewed_template_reused_verbatim':True,'pairs':37,'goals':74,'unsealed_errors':0,'sealed_errors':74,'one_rfl_error_per_goal':True,'synthetic_duplicate_drop':negative,'definition_order_matches_existing_effective_control_template':m['definitions'],'rows':coverage};(out/'control-coverage.json').write_text(json.dumps(controls,indent=2)+'\n')
foreign={'all_root_and_descendant_direct_def_entries':defs,'ordinary_foreign_definitions':sorted(ordinary),'ordinary_count':len(ordinary),'all_ordinary_foreign_defs_covered_by37seals':True,'structure_projection_abbrev_entries':sorted(abbrevs),'abbrev_count':len(abbrevs),'axiom_inventory':[{'name':n,'axioms':a.split(', ')} for n,a in ax],'roots':[{'name':n,'private':p=='true','simp':s=='true','unfold':u=='true'} for n,p,s,u in roots]};(out/'compiled-inventory.json').write_text(json.dumps(foreign,indent=2)+'\n');(out/'argument-review.json').write_text(json.dumps(argument_result,indent=2)+'\n')
p=Path(json.loads((out/'capture.json').read_text())['source']);actual=p.read_bytes();assert H(actual)==H(before)
# Only the contiguous proof-family block changes, including its three sketches.
oldstart=before.rfind('/--',0,before.index('private lemma fwdMap_backB'));oldend=before.rfind('/--',0,before.index('private lemma fwdMap_emit'))
newstart=source.rfind('/--',0,source.index('private lemma fwdMap_back '));newend=source.rfind('/--',0,source.index('private lemma fwdMap_emit'))
assert before[:oldstart]==source[:newstart] and before[oldend:]==source[newend:]
receipt={'candidate_sha256':H(source),'actual_source_sha256_before_and_after':H(actual),'actual_source_unchanged':True,'all_bytes_outside_exact_proof_family_block_identical':True,'full_native':{'receipt':'Candidate-native-v1-run.json','errors':0,'seconds':native['seconds']},'three_region_strong_seal':{'receipt':'Candidate-sealed-v2-run.json','errors':0,'seconds':sealed['seconds'],'definitions':37,'definition_simps_suppressed':3},'roots':3,'private_non_simp_roots':3,'additional_compiler_descendants':len(ax)-3,'standard_axiom_closures':len(ax),'ordinary_foreign_defs':len(ordinary),'fresh_controls':{'pairs':37,'unsealed_goals_passed':74,'sealed_expected_rfl_failures':74,'per_goal_multiplicity_verified':True,'duplicate_drop_rejected':True},'preserved_failure':{'receipt':'Candidate-sealed-v1-run.json','errors':3,'kind':'Only docstring/section wrapper syntax; corrected in v2 without changing candidate proofs.'},'claim_limit':'Inert copied source only. No actual source adoption, downstream replay, compiled before/after whole-module census, screen, cache/snapshot/Git write, commit/push, dispatch or clearance.'};(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));print('Foreign ordinary:',sorted(ordinary));print('Projection abbrevs:',sorted(abbrevs))
