from pathlib import Path
import json,re,hashlib,difflib,datetime
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4];WT=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');rel='TCSlib/Complexity/CookLevin/Hardness.lean';raw=(WT/rel).read_text();previous=ROOT/'campaign/gates/106-sg1-dedup/review/round3-extra-repairs'
assert hashlib.sha256(raw.encode()).hexdigest()==json.loads((previous/'context.json').read_text())['after_sha256']
(OUT/'Hardness-before.lean.txt').write_text(raw)
proposal=ROOT/'campaign/gates/106-sg1-dedup/review/prefix-import-proposal/Drop-v1.lean.txt';probe=proposal.read_text();body=probe.split(':= by\n',1)[1].split('\nend Complexity',1)[0]+'\n'
assert 'PrefixByLength.drop.eq_1' in body and 'eq_def' not in body
m=re.search(r'(?m)^private lemma clA5Drop_native\b',raw);ds=raw.rfind('/--',0,m.start());de=raw.index('-/',ds)+2;proof=raw.index(':= by',m.start())+len(':= by');eol=raw.index('\n',proof);end=raw.find('\n\n/--',eol)
header=raw[m.start():proof];olddoc=raw[ds:de];oldbody=raw[eol+1:end+1];newdoc='''/-- Removing as many leading bits as the length of a computed word is polynomial-time.
**Proof sketch.** Pair the length word first and the payload second, apply the public
prefix remover, and read its result through its equation and the public pair projections. -/'''
oldtoken=olddoc+'\n'+header+'\n'+oldbody;newtoken=newdoc+'\n'+header+'\n'+body;assert raw.count(oldtoken)==1;after=raw.replace(oldtoken,newtoken)
newimport='import TCSlib.Complexity.ClassNP.PolyTimePrefix\n';marker='import TCSlib.Complexity.ClassNP.SAT\n';assert newimport not in after and after.count(marker)==1;after=after.replace(marker,newimport+marker,1)
(OUT/'Hardness-after.lean.txt').write_text(after);(OUT/'Hardness.patch').write_text(''.join(difflib.unified_diff(raw.splitlines(True),after.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel)))
change={'name':'clA5Drop_native','old_doc':olddoc,'new_doc':newdoc,'header':header,'old_body':oldbody,'new_body':body,'new_import':newimport.strip(),'old_line':raw[:m.start()].count('\n')+1};(OUT/'change.json').write_text(json.dumps(change,indent=2)+'\n')
c={'status':'One user-approved import plus one authorized same-header proof/doc repoint; no additional source scope','worktree':str(WT),'snapshot':'/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-msg4','owned_file':rel,'before_sha256':hashlib.sha256(raw.encode()).hexdigest(),'after_sha256':hashlib.sha256(after.encode()).hexdigest(),'approved_import':'TCSlib.Complexity.ClassNP.PolyTimePrefix','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root_passed_proposal_sha256':hashlib.sha256(probe.encode()).hexdigest(),'supplied_base_HEAD':'478cd3a8dfb46094b9d8b971662f2ddadb1eccdb'};(OUT/'context.json').write_text(json.dumps(c,indent=2)+'\n')
prior=ROOT/'campaign/gates/106-sg1-dedup/review/round3-closure-repairs';(OUT/'run-probe.py').write_text((previous/'run-probe.py').read_text().replace('tcslib-g106-r3-extra-','tcslib-g106-r3-prefix-'))
guards=(previous/'guard-definitions.txt').read_text().splitlines()+['Complexity.PrefixByLength.drop'];attrs='attribute [local irreducible] '+' '.join(guards)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n';(OUT/'guard-definitions.txt').write_text('\n'.join(guards)+'\n');(OUT/'guard-attributes.txt').write_text(attrs)
meta=(previous/'metadata-appendix.lean.txt').read_text();meta=re.sub(r'let wanted : List String := \[[^\n]*\]','let wanted : List String := ["clA5Drop_native"]',meta);(OUT/'metadata-appendix.lean.txt').write_text(meta)
sealed=after.replace(newtoken,'section SG1PrefixSeal\n'+attrs+newtoken+'end SG1PrefixSeal\n');(OUT/'Hardness-native-v1.lean.txt').write_text(after+meta);(OUT/'Hardness-sealed-v1.lean.txt').write_text(sealed+meta)
small='import TCSlib.Complexity.ClassNP.PolyTimePrefix\nset_option maxHeartbeats 0\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n'+attrs+'\nnamespace Complexity\nopen Turing\n'+newtoken+'\nend Complexity\n'+meta
small+='''\nopen Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let n := `Complexity.PrefixByLength.drop.eq_1
  let some info := env.find? n | throwError "Serialized reader absent before any reserved-name query"
  let axs ← liftCoreM <| Lean.collectAxioms n
  let owner := (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)
  logInfo m!"SERIALIZED_READER|{n}|owner={owner}|AX={axs}|type={info.type}"
'''
(OUT/'Preapply-sealed-v1.lean.txt').write_text(small)
# Fresh whole-guard calibration avoids relying on implicit identity of old contexts.
for mode in ['unsealed','sealed']:
 s=(previous/('Controls-'+mode+'-v1.lean.txt')).read_text().replace('import TCSlib.Complexity.ClassNP.NP','import TCSlib.Complexity.ClassNP.PolyTimePrefix')
 a=s.index('  let names : List Name :=');b=s.index('\n  let mut index :=',a);s=s[:a]+'  let names : List Name := ['+',\n    '.join('`'+n for n in guards)+']'+s[b:]
 if mode=='sealed':line=next(x for x in s.splitlines(True) if x.startswith('attribute [local irreducible]'));s=s.replace(line,attrs.splitlines(True)[0])
 s=s.replace('g106_extra_controls','g106_prefix_controls').replace('G106ExtraRflControl','G106PrefixRflControl');(OUT/('Controls-'+mode+'-v1.lean.txt')).write_text(s)
(OUT/'control-definitions.txt').write_text('\n'.join(guards)+'\n');(OUT/'check-controls.py').write_text((previous/'check-controls.py').read_text())
print(json.dumps({'after_sha256':c['after_sha256'],'new_import':c['approved_import'],'proof_names':['clA5Drop_native'],'guard_count':len(guards)},indent=2))
