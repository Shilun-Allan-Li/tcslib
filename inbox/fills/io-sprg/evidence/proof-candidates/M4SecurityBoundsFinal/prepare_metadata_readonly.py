from pathlib import Path
import csv,hashlib,io,json,re
B=Path('/private/tmp/io-sprg-proof-notes/M4SecurityBounds')
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
head='''import TCSlib.Cryptography.Games.Advantage
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 100000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open TCSlib.Cryptography TCSlib.Cryptography.Games

'''
interface='''example {LA GA BL BG : Type}
    (C : ℕ → Bool → ℕ → ProbComp Bool)
    (relL : LA → BL → Prop) (relG : GA → BG → Prop)
    (aL : BL → ℕ → ℝ) (aG : BG → ℕ → ℝ)
    (hLPN : ∀ (tails : ℕ → Bool) (hops : (κ : ℕ) → Fin (κ + 1)),
      ∃ ω : LA, ∀ B : BL, relL ω B → ∀ κ, (hops κ).val < κ →
        advantage (C κ (tails κ) (hops κ).val)
          (C κ (tails κ) ((hops κ).val + 1)) ≤ aL B κ)
    (hPRG : ∃ ω : GA, ∀ B : BG, relG ω B → ∀ κ,
      advantage (C κ true κ) (C κ false κ) ≤ aG B κ)'''
goals={
 'lemma42_core':interface+''' :
    ∃ ωL : LA, ∃ ωG : GA, ∀ L : BL, ∀ G : BG,
      relL ωL L → relG ωG G → ∀ κ,
        advantage (C κ true 0) (C κ false κ) ≤ (κ : ℝ) * aL L κ + aG G κ''',
 'prop41_core':interface+'''
    (H0 H1 H2 H3 : ℕ → ProbComp Bool) (raw err : ℕ → ℝ)
    (hraw : ∀ κ, raw κ = advantage (H0 κ) (H3 κ))
    (hreal : ∀ κ, accept (H1 κ) = accept (C κ true 0))
    (huniform : ∀ κ, accept (H2 κ) = accept (C κ false 0))
    (hstatR : ∀ κ, advantage (H0 κ) (H1 κ) ≤ err κ)
    (hstatU : ∀ κ, advantage (H2 κ) (H3 κ) ≤ err κ) :
    ∃ ωL : LA, ∃ ωG : GA, ∀ L : BL, ∀ G : BG,
      relL ωL L → relG ωG G → ∀ κ,
        raw κ ≤ 2 * (κ : ℝ) * aL L κ + aG G κ + 2 * err κ''',
 'single_chain_selector_control':'''example (C : ℕ → ℕ → ProbComp Bool) :
    ∀ κ : ℕ, ∃ i : Fin (κ + 1), 0 < κ → i.val < κ ∧
      advantage (C κ 0) (C κ κ) ≤
        (κ : ℝ) * advantage (C κ i.val) (C κ (i.val + 1))''',
 'two_tail_selector_control':'''example (C : ℕ → Bool → ℕ → ProbComp Bool) :
    ∀ κ : ℕ, ∃ b : Bool, ∃ i : Fin (κ + 1), 0 < κ → i.val < κ ∧
      ∀ (tail : Bool) (j : ℕ), j < κ →
        advantage (C κ tail j) (C κ tail (j + 1)) ≤
          advantage (C κ b i.val) (C κ b (i.val + 1))'''
}
requests=[]
for name,goal in goals.items():
 p=B/'overlap/templates'/(name+'.lean.template');p.write_text(head+goal+' := __PROBE_BODY__\n')
 requests.append({'name':name,'template':'templates/'+p.name,'status':'UNRUN',
 'scope':'FULL_STRONG_HOP_COMPOSITION_CORE' if name in ['lemma42_core','prop41_core'] else 'SUPPLEMENTAL_SELECTOR_CONTROL_NOT_NEW_SOURCE_HELPER',
 'actual_declaration':name.removesuffix('_core') if name.endswith('_core') else 'LOCAL_SELECTOR_ONLY',
 'owned_imports':[],'universe':'Type0','template_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'namespace_openings':'Both fully qualified openings are defined by Games.Advantage import'})
 text=p.read_text();assert text.count('__PROBE_BODY__')==1 and 'Type*' not in text
 assert 'StructuredSeed' not in '\n'.join(re.findall(r'^import (\S+)',text,re.MULTILINE))
 stack=[]
 for c in text:
  if c in '([{':stack.append(c)
  elif c in ')]}':assert stack and '([{'.index(stack.pop())==')]}'.index(c),(name,c)
 assert not stack,(name,stack)
(B/'overlap/probe-index.json').write_text(json.dumps(requests,indent=2)+'\n')
(B/'overlap/names.txt').write_text('lemma42_core\nprop41_core\n')
(B/'overlap/control-names.txt').write_text('single_chain_selector_control\ntwo_tail_selector_control\n')
source=W/'TCSlib/Cryptography/Obfuscation/StructuredSeed/Security.lean';s=source.read_text()
rows=[]
frozen=list(csv.DictReader((W/'evidence/statements/proof-obligations-current.tsv').open(),delimiter='\t'))
for name in ['lemma42','prop41']:
 match=re.search(r'^theorem '+name+r'\b[\s\S]*? := sorry',s,re.MULTILINE);assert match,name
 (B/(name+'.statement.txt')).write_text(match.group(0)+'\n')
 r=next(r for r in frozen if r['Lean_name'].endswith('.'+name))
 text=(B/(name+'.proof')).read_text();assert len(re.findall(r'\bby\b',text))==1
 assert not re.search(r'\b(sorry|admit)\b',text) and max(map(len,text.splitlines()))<=100
 rows.append(dict(r,candidate=name+'.proof',candidate_lines=len(text.splitlines()),
 candidate_sha256=hashlib.sha256(text.encode()).hexdigest(),status='UNRUN'))
stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=list(rows[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(rows)
(B/'frozen-obligation-map.tsv').write_text(stream.getvalue())
refs=['TCSlib/Cryptography/Obfuscation/StructuredSeed/Security.lean',
 'TCSlib/Cryptography/Obfuscation/StructuredSeed/Hybrids.lean',
 'TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/LPN.lean',
 'TCSlib/Cryptography/Obfuscation/StructuredSeed/Reductions/PRG.lean',
 'TCSlib/Cryptography/Obfuscation/StructuredSeed/Defs.lean',
 'TCSlib/Cryptography/Games/Advantage.lean',
 'TCSlib/Cryptography/Foundations/Probability.lean',
 '.lake/packages/mathlib/Mathlib/Data/Finset/Max.lean',
 'evidence/statements/proof-obligations-current.tsv']
(B/'source-bindings.json').write_text(json.dumps({'status':'STATIC_TEXT_REVIEW_NO_LEAN',
 'files_sha256':{r:hashlib.sha256((W/r).read_bytes()).hexdigest() for r in refs}},indent=2)+'\n')
m5=json.loads(Path('/private/tmp/io-sprg-proof-notes/M5SecurityPrepared/summary.json').read_text())
added=sum(int(r['candidate_lines'])-1 for r in rows)
(B/'summary.json').write_text(json.dumps({'status':'FULL_UNRUN_BODIES',
 'original_M4_bodies':2,'new_public_helpers':0,'candidate_lines':{r['Lean_name'].split('.')[-1]:r['candidate_lines'] for r in rows},
 'proof_holes':0,'tactic_blocks_per_body':1,'original_public_only_cores':2,
 'supplemental_controls':2,'source_imports_added':[],
 'Security_lines_with_all_7_M5_and_both_M4_bodies':m5['Security_lines_after_only_these_M5_replacements']+added,
 'size_qualification':'Exact source-line arithmetic for staged strings only, excluding future repairs/docs; no split needed by this known payload'},indent=2)+'\n')
print('Two full original bodies + two full strong-interface cores + two selector controls staged.')
