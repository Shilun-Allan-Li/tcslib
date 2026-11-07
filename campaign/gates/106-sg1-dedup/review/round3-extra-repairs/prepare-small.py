from pathlib import Path
import json,re,hashlib,datetime
OUT=Path(__file__).resolve().parent;ROOT=OUT.parents[4];WT=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4');rel='TCSlib/Complexity/CookLevin/Hardness.lean';src=WT/rel;raw=src.read_text();prior=ROOT/'campaign/gates/106-sg1-dedup/review/round3-closure-repairs'
assert hashlib.sha256(raw.encode()).hexdigest()==json.loads((prior/'context.json').read_text())['files'][rel]['after_sha256']
(OUT/'Hardness-before.lean.txt').write_text(raw)
(OUT/'run-probe.py').write_text((prior/'run-probe.py').read_text().replace('tcslib-g106-r3-closure-','tcslib-g106-r3-extra-'))
ctx={'status':'Two specifically authorized additional private proof-only repoints; test before apply','worktree':str(WT),'snapshot':'/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-scratch/oleans-msg4','owned_file':rel,'before_sha256':hashlib.sha256(raw.encode()).hexdigest(),'source_parent_uncommitted_base':'478cd3a8dfb46094b9d8b971662f2ddadb1eccdb','at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()};(OUT/'context.json').write_text(json.dumps(ctx,indent=2)+'\n')
headdefs=[]
for name in ['clHeaderTail','clHeaderField']:
 m=re.search(r'(?m)^private def '+name+r'\b',raw);end=raw.find('\n\n/--',m.start());headdefs.append(raw[m.start():end+1])
(OUT/'owner-local-context.lean.txt').write_text('\n'.join(headdefs))
body1='''  change (((pairDecode w).map Prod.fst).getD []).length ≤ w.length ∧
    (((pairDecode w).map Prod.snd).getD []).length ≤ w.length
  cases hd : pairDecode w with
  | none =>
    simp only [hd, Option.map_none, Option.getD_none, List.length_nil]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | some p =>
    rcases p with ⟨a, b⟩
    have hlen := congrArg List.length (eq_pairEncode_of_pairDecode w a b hd)
    rw [length_pairEncode] at hlen
    simp only [hd, Option.map_some, Option.getD_some]
    constructor <;> omega
'''
body2='''  have h := polyTimeComputable_lenLe.comp (hg.pairEncode hf)
  convert h using 1
  funext x
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
'''
docs={'clA5Pair_sizes':'''/-- Both decoded components are bounded by their complete source word, with empty
defaults on malformed input.
**Proof sketch.** Split the decode once. On success the public inverse identifies
an encoded pair, whose published length bounds both components; failure gives empty words. -/''','clA5Le_native':'''/-- Unary comparison is polynomial-time by comparing the lengths of a reversed pair
of the two unary words, using `Complexity.polyTimeComputable_lenLe`. -/'''}
changes=[]
for name,body in [('clA5Pair_sizes',body1),('clA5Le_native',body2)]:
 m=re.search(r'(?m)^private lemma '+name+r'\b',raw);ds=raw.rfind('/--',0,m.start());de=raw.index('-/',ds)+2;proof=raw.index(':= by',m.start())+len(':= by');eol=raw.index('\n',proof);end=raw.find('\n\n/--',eol)
 changes.append({'name':name,'old_line':raw[:m.start()].count('\n')+1,'header':raw[m.start():proof],'old_doc':raw[ds:de],'new_doc':docs[name],'old_body':raw[eol+1:end+1],'new_body':body})
(OUT/'changes-proposed.json').write_text(json.dumps(changes,indent=2)+'\n')
guards=(prior/'guard-definitions.txt').read_text().splitlines()+['Complexity.pairFstD','Complexity.pairSndD'];attrs='attribute [local irreducible] '+' '.join(guards)+'\nattribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n';(OUT/'guard-definitions.txt').write_text('\n'.join(guards)+'\n');(OUT/'guard-attributes.txt').write_text(attrs)
context='\nnamespace Complexity\nopen Turing\n'+ '\n'.join(headdefs)+'\n'
proofs='\n'.join(r['new_doc']+'\n'+r['header']+'\n'+r['new_body'] for r in changes)+'\nend Complexity\n'
meta=(prior/'Hardness-final-native.lean.txt').read_text();pos=meta.rfind('\nopen Lean Elab Command Meta in\nrun_cmd do');meta=meta[pos:];meta=re.sub(r'let wanted : List String := \[[^\n]*\]', 'let wanted : List String := '+json.dumps([r['name'] for r in changes]),meta)
(OUT/'metadata-appendix.lean.txt').write_text(meta)
imports='import TCSlib.Complexity.ClassNP.NP\nset_option maxHeartbeats 0\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n'
(OUT/'Small-native-v1.lean.txt').write_text(imports+context+proofs+meta)
(OUT/'Small-sealed-v1.lean.txt').write_text(imports+attrs+context+proofs+meta)
print('Prepared exact two headers and unchanged same-home definition slices; no source edit applied.')
