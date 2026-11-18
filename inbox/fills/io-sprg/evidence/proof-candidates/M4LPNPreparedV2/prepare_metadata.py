from pathlib import Path
import csv,difflib,hashlib,io,json,re,subprocess
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange');B=Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared');O=Path('/private/tmp/io-sprg-proof-notes/LPNHopFinal')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
items=json.loads((B/'overlap/exact-probe-index.json').read_text());checks=[];spec=[]
def bal(s):
 stack=[];pairs={')':'(',']':'[','}':'{'}
 for c in s:
  if c in '([{':stack.append(c)
  elif c in ')]}':
   if not stack or stack.pop()!=pairs[c]:return False
 return not stack
for r in items:
 p=Path(r['candidate']);s=p.read_text();code=re.sub(r'/-[\s\S]*?-/', '',s)
 c={'index':r['index'],'file':p.name,'lines':len(s.splitlines()),'max_line':max(map(len,s.splitlines())),'outer_by_count':len(re.findall(r'\bby\b',code)),'explicit_holes':len(re.findall(r'\b(?:sorry|admit)\b',code)),'balanced':bal(code)}
 assert c['outer_by_count']==1 and c['explicit_holes']==0 and c['balanced'] and c['max_line']<=100,c
 for i,l in enumerate(code.splitlines()):
  if not re.match(r'^\s*(?:[·|]\s*)?have\b',l):continue
  header=l
  if ':' not in header or ':=' in header:continue
  col=l.index('have')
  for nxt in code.splitlines()[i+1:]:
   if ':=' in header:break
   if nxt.strip().startswith('·') and len(nxt)-len(nxt.lstrip())==col:break
   header+='\n'+nxt
  assert ':=' in header,(p.name,i+1)
 c['typed_have_scan']='PASS_INCLUDING_BULLET_PREFIXES';checks.append(c)
 old=O/p.name;diff=''.join(difflib.unified_diff(old.read_text().splitlines(True),s.splitlines(True),fromfile=str(old),tofile=str(p)));(B/(p.name+'.diff')).write_text(diff)
 row=dict(r,old_candidate=str(old),old_candidate_sha256=sha(old),docstring_sha256=hashlib.sha256(s.split('-/',1)[0].encode()).hexdigest() if r['index']<10 else None,status='FULL_UNRUN_BODY')
 row['root_pretest_focus']={1:'Mandatory shared runAt coin bridge, then pure prefix reader.',2:'Canonical family advantage/encoding readers.',3:'Matrix.of arrow transport; exact coordinate projections.',4:'Canonical Q/noise equalities and the final two pointwise cast/sum simp goals.',5:'Selected repetition and chain order split.',6:'Fixed Boolean offset and next-chain order split.',7:'Typed combined seed/coin uprob equivalence and exact sample coordinates.',8:'Typed combined coordinate/coin relabelling; fixed-seed translation hnorm/htranslate.',9:'Typed hsplit/hmove/resampling; actual chain normalization hchain; no broad generic simp_rw.',10:'Single global advice family before B, with sentinel/off-image branches.'}[r['index']]
 spec.append(row)
(B/'root-helper-specs.json').write_text(json.dumps({'status':'PROPOSED_UNRUN_HEADERS_AND_BODIES_NOT_SOURCE_IMPLEMENTATION','placement_approval':'Root approved Sections05–08 before helper landing; existing frozen lpn_hop stays Hop.','new_helper_count':9,'frozen_original_count':1,'helpers_and_original':spec},indent=2)+'\n')
stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=['index','name','original_or_new','placement','candidate','candidate_sha256','header_sha256','exact_status','apply_status'],delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows({k:r[k] for k in writer.fieldnames} for r in items);(B/'root-placement-index.tsv').write_text(stream.getvalue())
for p in (B/'overlap').rglob('*.template'):
 s=p.read_text();assert bal(s) and s.count('__PROBE_BODY__')==1,p
 assert max(map(len,s.splitlines()))<=100,p
 assert not re.search(r'\bType\*',s),p
 if p.parent.name=='exact-statements':
  im=[l[7:] for l in s.splitlines() if l.startswith('import ')];assert im==['TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN.Defs','Lean.Elab.Tactic.LibrarySearch'],p
# The one M0 original retains its globally frozen normalized header.
frozen=json.loads((W/'evidence/checks/m3-final/global-freeze/frozen-global-map.json').read_text());header=(B/'10-lpn_hop.statement.txt').read_text().strip();name=items[-1]['name'];assert ' '.join(header.split())==frozen[name]['normalized_header']
(B/'static-checks.json').write_text(json.dumps({'status':'STATIC_ONLY_NOT_LEAN','candidate_checks':checks,'all_nine_new_helper_headers_unchanged_from_previous_packet':True,'frozen_lpn_hop_header_and_prose_unchanged':True,'exact_statement_templates':10,'public_only_composition_templates':3,'all_search_statuses':'NOT_RUN'},indent=2)+'\n')
api={
'TCSlib/Cryptography/Asymptotic/Realization.lean':'_root_.Complexity.NUPPT.RealizesOn.runAt_coinsEquivPoly_symm _root_.Complexity.NUPPT.RealizesOn.coins_eq',
'TCSlib/Cryptography/Asymptotic/Adversary.lean':'_root_.Complexity.NUPPT.distinguisherL_eq',
'TCSlib/Complexity/Randomized/PPT.lean':'runAt_eq',
'TCSlib/Cryptography/Foundations/Probability.lean':'uprob_prod uprob_comp_equiv',
'TCSlib/Cryptography/HardcoreBit/Basic.lean':'pushesUniform_restrict pushesUniform_add_right pushesUniform_iff PushesUniform.uprob_eq',
'TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean':'ofFn_castLE_eq_take',
'TCSlib/Cryptography/Games/Bridges/Experiments.lean':'prob_sample_eq_uprob expect_sample_eq_uexp expect_sample_pair',
'TCSlib/Cryptography/Games/Probability.lean':'prob_eq_expect expect_bind expect_map expect_pure expect_sample_comm expect_sample_update abs_expect_sub_le_expect',
'TCSlib/Cryptography/Authentication/Signatures/Lamport/Averaging.lean':'exists_expect_sample_le',
'TCSlib/Cryptography/LWE/Basic.lean':'sample_fst sample_snd noisyValues_apply',
'TCSlib/Cryptography/Obfuscation/StructuredSeed/LPN.lean':'lpnNoise_coins noise_eq toLWE_noise',
'TCSlib/Cryptography/Obfuscation/StructuredSeed/Params.lean':'kappaOf_le kappaOf_pow lpnFamily_raw_noiseDen lpnFamily_raw_modulus W_eq_noiseDenAt n_eq',
'TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Defs.lean':'lpnEnc_eq lpnChalEquiv_eq lpn_dimension_eq lpn_samples_eq lpn_modulus_eq lpnMatrixAt_eq lpnValuesAt_eq lpnPre_eq lpnRed_eq',
'TCSlib/Cryptography/Obfuscation/StructuredSeed/Samplers.lean':'noiseValue_eq idSamp\x27_eq idCore_eq',
'TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean':'chainGame_eq chainPublic_eq',
'.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean':'of'}
a=[];bindings={}
for filename,names in api.items():
 p=W/filename;s=p.read_text();bindings[filename]=sha(p)
 for leaf in names.split():
  hits=[(i,l) for i,l in enumerate(s.splitlines(),1) if re.search(r'\b(?:theorem|lemma|def) '+re.escape(leaf)+r'(?=\s|\()',l)]
  assert hits,(filename,leaf)
  for i,l in hits:a.append({'name':leaf,'source_anchor':filename+':'+str(i),'declaration_line':l.strip(),'source_sha256':sha(p)})
stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=list(a[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(a);(B/'APIs.tsv').write_text(stream.getvalue())
for leaf in ('Defs','Encoding','Transport','Sections','Hop'):
 p=W/('TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/'+leaf+'.lean');bindings[str(p.relative_to(W))]=sha(p)
(B/'source-bindings.json').write_text(json.dumps({'scope':'READ_ONLY_SOURCE_BYTES_AND_ROOT_REPORTED_PROGRESS_NOT_KERNEL_AUDIT','source_sha256':bindings,'MRr3':'Verdict01 MUST use NUPPT.distinguisherL_eq then hB.runAt_coinsEquivPoly_symm then lpnRed_eq; it does.','prefix_reader':'OneWay.ofFn_castLE_eq_take is pure, already transitive via OneWayLemmas; no forbidden facade import is proposed.','source_equation_and_algorithm_scope':'Only owner readers, Core/Mathlib computation and proof-local abbreviations are expanded. No algorithm, encoder, machine or sampler is defined.','root_progress_provenance':'Root reported published M3 2a9ccadc,34 owners after approved Sections split; this packet does not query Git or claim those builds itself.'},indent=2)+'\n')
counts={r['index']:c['lines'] for r,c in zip(items,checks)};sizes={}
for leaf,indices in [('Transport',range(1,5)),('Sections',range(5,9)),('Hop',[9])]:
 p=W/('TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/'+leaf+'.lean');base=len(p.read_text().splitlines());sizes[leaf]={'current_skeleton_lines':base,'added_helper_candidate_lines':sum(counts[n] for n in indices),'known_assembly_lines_before_separator_adjustment':base+sum(counts[n] for n in indices)+(counts[10]-1 if leaf=='Hop' else 0)}
(B/'line-budget.json').write_text(json.dumps({'status':'TEXT_ESTIMATE_NOT_IMPLEMENTED_NOT_CHECKED','approved_owner_placement':sizes,'new_Sections_external_roots':0,'extra_M0_decl_moves_for_Sections':0,'reason':'Previous unsplit Hop known590 lines before growth; approved future05–08 placement in Sections keeps each owner below600.'},indent=2)+'\n')
S=B/'searches';S.mkdir(exist_ok=True);queries=[('mandatory-coin-prefix',['rg','-n','runAt_coinsEquivPoly_symm|ofFn_castLE_eq_take|pushesUniform_restrict','TCSlib/Cryptography/Asymptotic/Realization.lean','TCSlib/Cryptography/Asymptotic/OneWayLemmas.lean','TCSlib/Cryptography/HardcoreBit/Basic.lean']),('probability-public-compositions',['rg','-n','theorem (expect_sample_pair|expect_sample_comm|expect_sample_update|expect_sample_equiv|exists_expect_sample_le)|def of :','TCSlib/Cryptography/Games/Probability.lean','TCSlib/Cryptography/Games/Bridges/Experiments.lean','TCSlib/Cryptography/Authentication/Signatures/Lamport/Averaging.lean','.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Defs.lean']),('canonical-sample-readers',['rg','-n','theorem (sample_fst|sample_snd|noisyValues_apply)|theorem (lpnMatrixAt_eq|lpnValuesAt_eq|lpnChalEquiv_eq)','TCSlib/Cryptography/LWE/Basic.lean','TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN/Defs.lean'])]
logs=[]
for name,args in queries:
 p=subprocess.run(args,cwd=W,capture_output=True,text=True);assert p.returncode in (0,1)
 q=S/(name+'.log');q.write_text('ARGS: '+repr(args)+'\nEXIT: '+str(p.returncode)+'\nSTDOUT:\n'+p.stdout+'\nSTDERR:\n'+p.stderr);logs.append({'id':name,'args':args,'exit_code':p.returncode,'classification':'STATIC_TEXT_HITS' if p.returncode==0 else 'BOUNDED_TEXT_NO_HIT_NOT_LIBRARY_ABSENCE','log':str(q),'sha256':sha(q)})
(B/'static-search-index.json').write_text(json.dumps(logs,indent=2)+'\n')
print('Packet metadata ready:',len(a),'API anchors;',sizes)
