from pathlib import Path
import csv,hashlib,io,json,re
B=Path('/private/tmp/io-sprg-proof-notes/M4PRGPrepared')
W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
common=['TCSlib.Cryptography.Games.Hopping','TCSlib.Cryptography.Games.Bridges.Experiments','Lean.Elab.Tactic.LibrarySearch']
base='''set_option maxHeartbeats 100000
set_option relaxedAutoImplicit false
set_option autoImplicit false

open TCSlib.Cryptography TCSlib.Cryptography.Games

'''
goals={}
def add(name,goal,actual,kind,readers,extra=(),scope='COMPONENT_CORE_ACTUAL_READERS_ABSTRACTED'):
 imports=common+list(extra)
 text=''.join('import '+m+'\n' for m in imports)+'\n'+base+goal+' := __PROBE_BODY__\n'
 p=B/'overlap/templates'/(name+'.lean.template');p.write_text(text)
 goals[name]={'name':name,'template':'templates/'+p.name,'actual_declaration':actual,
  'kind':kind,'actual_reader_mapping':readers,'imports':imports,'status':'UNRUN',
  'scope':scope,'template_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
add('sdCore_publicSeed_core','''example {Pub Block F : Type} (e : Block ⊕ Unit ≃ Pub)
    (inst : Block → F) (flag : F) (packed : Pub → F)
    (public : (Block → F) → F → Pub → F)
    (hpack : ∀ p, packed p = match e.symm p with | .inl k => inst k | .inr _ => flag)
    (hpub : ∀ blocks err p,
      public blocks err p = match e.symm p with | .inl k => blocks k | .inr _ => err) :
    packed = public inst flag''','Params.sdCore_publicSeed','NEW_HELPER',
 'sdCore_seed/instances/err + packSeed_fst + publicSeed_eq, e=pubEquiv; flag=err.toNat field value')
for name,actual in [('hyb_real_prg_le_core','Params.hyb_real_prg_le'),('hyb_uniform_random_le_core','Params.hyb_uniform_random_le')]:
 add(name,'''example {Ω : Type} (c : ProbComp Ω) (left right bad : Ω → Prop)
    (hagree : ∀ z, ¬ bad z → (left z ↔ right z)) :
    |ProbComp.prob c left - ProbComp.prob c right| ≤ ProbComp.prob c bad''',actual,'FROZEN_M4_ORIGINAL',
 'Actual retained IdDraw/Draw/Tail/coins coupling; sdCore_publicSeed; real/prg additionally G4_eval_sdCore + eval_eq; abs_prob_sub_le_of_agree',
 scope='EXACT_PUBLIC_AGREE_OFF_BAD_BOUND; actual law and deterministic reader normalization remain explicit source obligations')
add('prg_verdict_prob_core','''example {C : Type} [Fintype C] [Nonempty C] (short long : ℕ)
    (hcut : short ≤ long) (e : C ≃ (Fin long → Bool))
    (Q : List Bool → Prop) (verdict : C → Prop)
    (hreader : ∀ r, verdict r ↔ Q ((List.ofFn (e r)).take short)) :
    ProbComp.prob (ProbComp.sample C) verdict =
      ProbComp.prob (ProbComp.sample (Fin short → Bool)) (fun r => Q (List.ofFn r))''',
 'Params.prg_verdict_prob','NEW_HELPER',
 'RealizesOn.coins_eq/distinguisherL_eq + coinsEquivPoly_symm_ofFn + prgRed_eq; short≤long from kappaOfN_le/PolyExpr.eval_mono; restriction and list-prefix readers',
 extra=['TCSlib.Cryptography.HardcoreBit.Basic','TCSlib.Cryptography.Asymptotic.OneWayLemmas'])
add('prg_nuisance_average_core','''example {G I Seed Rep Buck Mat U Advice : Type}
    [Fintype G] [Nonempty G] [Fintype Seed] [Nonempty Seed]
    [Fintype Rep] [Nonempty Rep] [Fintype Buck] [Nonempty Buck]
    [Fintype Mat] [Nonempty Mat] [Fintype U] [Nonempty U]
    [Fintype Advice] [Nonempty Advice] (idCore : G → I)
    (e : Advice ≃ Buck × (Mat × U)) (f : I → Seed → Buck → Mat → U → ℝ) :
    ProbComp.expect (ProbComp.sample (G × (Buck × Mat))) (fun a =>
      ProbComp.expect (ProbComp.sample (Seed × Rep)) (fun d =>
        ProbComp.expect (ProbComp.sample U) (fun u => f (idCore a.1) d.1 a.2.1 a.2.2 u))) =
      ProbComp.expect (ProbComp.sample Advice) (fun ω =>
        ProbComp.expect (ProbComp.sample G) (fun g =>
          ProbComp.expect (ProbComp.sample Seed) (fun σ =>
            f (idCore g) σ (e ω).1 (e ω).2.1 (e ω).2.2)))''',
 'Params.prg_nuisance_average','NEW_HELPER',
 'idSamp_eq/idCore_eq and G.idSamp_eq; Draw=Seed×Rep; PRGAdvice.prodEquiv; no Fintype I or sample I is assumed',scope='FULL_FINITE_LAW_CORE_AFTER_PUBLIC_TYPE_AND_MAP_READERS')
add('prg_chain_output_reindex_core','''example (m n : ℕ) (h : m = n) (F : (Fin m → Bool) → ℝ) :
    ProbComp.expect (ProbComp.sample (Fin m → Bool)) F =
      ProbComp.expect (ProbComp.sample (Fin n → Bool))
        (fun v => F (fun j => v ((finCongr h) j)))''',
 'Params.prg_chain_accept_average','NEW_HELPER',
 'm_eq/outputIndex_eq yield explicit comparison-vector arrow equivalence; predecessor nuisance helper handles remaining law, prgPre_eq/kappaOfN_n handles image guard',
 scope='OUTPUT_VECTOR_CORE; actual nuisance specialization, image guard and read-only challenge normalization remain explicit source obligations')
add('prg_hop_fix_advice_core','''example (Advice : ℕ → Type) [∀ n, Fintype (Advice n)]
    [∀ n, Nonempty (Advice n)] (image : ℕ → Prop)
    (a b : ℕ → ℝ) (f g : (n : ℕ) → Advice n → ℝ)
    (hreal : ∀ n, image n → a n = ProbComp.expect (ProbComp.sample (Advice n)) (f n))
    (huniform : ∀ n, image n → b n = ProbComp.expect (ProbComp.sample (Advice n)) (g n)) :
    ∃ ω : (n : ℕ) → Advice n, ∀ n, image n → |a n - b n| ≤ |f n (ω n) - g n (ω n)|''',
 'Params.prg_hop','FROZEN_M4_ORIGINAL',
 'prg_chain_accept_average supplies hreal/huniform; abs_expect_sub_le_expect + exists_expect_sample_le; select full family before B, then prg_verdict_prob and kappaOfN_n',
 extra=['TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging'])
raw_head='''example {D S I X Seed Tail Coins : Type}
    (idDraw : ProbComp D) (sdDraw : ProbComp S) (tails : ProbComp Tail)
    (coins : ProbComp Coins) (idCore : D → I) (fullCore : I → S → X)
    (seed : X → Seed) (verdict : I → Seed → Tail → Coins → Bool)'''
add('hyb_real_eq_raw_core',raw_head+'''
    (output : I → Seed → Tail) :
    ((idCore <$> idDraw).bind fun i =>
      (fullCore i <$> sdDraw).bind fun x =>
      tails.bind fun _w => coins.bind fun r =>
        pure (verdict i (seed x) (output i (seed x)) r)) =
      ((idCore <$> idDraw).bind fun i =>
        ((fun s => seed (fullCore i s)) <$> sdDraw).bind fun z =>
        tails.bind fun _w => coins.bind fun r => pure (verdict i z (output i z) r))''',
 'Params.hyb_real_eq_raw','FROZEN_M4_ORIGINAL',
 'hyb_eq + Raw.game_eq + jlsSPRG_raw readers + derived id/sd sampler readers + challenge encoding readers; all four exact queries retained',scope='FULL_MONADIC_MAP_FUSION_CORE_AFTER_FROZEN_FIELD_AND_ENCODING_READERS')
add('hyb_random_eq_raw_core',raw_head+''' :
    ((idCore <$> idDraw).bind fun i =>
      (fullCore i <$> sdDraw).bind fun x =>
      tails.bind fun w => coins.bind fun r => pure (verdict i (seed x) w r)) =
      ((idCore <$> idDraw).bind fun i =>
        ((fun s => seed (fullCore i s)) <$> sdDraw).bind fun z =>
        tails.bind fun w => coins.bind fun r => pure (verdict i z w r))''',
 'Params.hyb_random_eq_raw','FROZEN_M4_ORIGINAL',
 'Same full map-fusion core, comparison output is literal shared tail; no unused query removed',scope='FULL_MONADIC_MAP_FUSION_CORE_AFTER_FROZEN_FIELD_AND_ENCODING_READERS')
unused='''example {I D U Tail Coins : Type} [Fintype U] [Nonempty U]
    (idx : ProbComp I) (draw : I → ProbComp D) (tails : ProbComp Tail)
    (coins : ProbComp Coins) (verdict : I → D → Tail → Coins → Bool) :
    accept (idx.bind fun i => (draw i).bind fun d =>
      tails.bind fun w => coins.bind fun r => pure (verdict i d w r)) =
      accept (idx.bind fun i => (draw i).bind fun d =>
        (ProbComp.sample U).bind fun _u =>
        tails.bind fun w => coins.bind fun r => pure (verdict i d w r))'''
for name,actual in [('hyb_prg_accept_eq_chain_zero_core','Params.hyb_prg_accept_eq_chain_zero'),('hyb_uniform_accept_eq_chain_zero_core','Params.hyb_uniform_accept_eq_chain_zero')]:
 add(name,unused,actual,'FROZEN_M4_ORIGINAL',
 'hyb_eq/chainGame_eq/sdSampFull_eq/sdCore_instances/σ/oneSd_pub/lpnVector_eq; chainPublic0 ignores U; semantic expect_const only',
 scope='FULL_UNUSED_QUERY_ACCEPTANCE_CORE_AFTER_LITERAL_DRAW_AND_VECTOR_READERS')
(B/'overlap/probe-index.json').write_text(json.dumps(list(goals.values()),indent=2)+'\n')
(B/'overlap/names.txt').write_text('\n'.join(goals)+'\n')
assert len(goals)==11
frozen=list(csv.DictReader((W/'evidence/statements/proof-obligations-current.tsv').open(),delimiter='\t'))
rows=[]
covered={v['actual_declaration'] for v in goals.values() if v['kind']=='FROZEN_M4_ORIGINAL'}
for r in frozen:
 if not r['milestone'].startswith('M4'):continue
 short=r['Lean_name'].removeprefix('TCSlib.Cryptography.Obfuscation.StructuredSeed.')
 rows.append(dict(r,packet_coverage='CANDIDATE_STAGED_UNRUN' if short in covered else 'OUTSIDE_THIS_PACKET'))
assert len(rows)==16 and sum(r['packet_coverage']=='CANDIDATE_STAGED_UNRUN' for r in rows)==7
stream=io.StringIO();writer=csv.DictWriter(stream,fieldnames=list(rows[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(rows)
(B/'frozen-M4-obligation-map.tsv').write_text(stream.getvalue())
checks=[]
for name,row in goals.items():
 p=B/'overlap'/row['template'];text=p.read_text()
 assert 'StructuredSeed' not in '\n'.join(row['imports'])
 assert 'Type*' not in text
 assert text.count('__PROBE_BODY__')==1
 stack=[]
 for c in text:
  if c in '([{':stack.append(c)
  elif c in ')]}':assert stack and '([{'.index(stack.pop())==')]}'.index(c),(name,c)
 assert not stack,(name,stack)
 checks.append({'name':name,'balanced_delimiters':True,'Type0':True,'owned_imports':[],
 'namespace_opening':'TCSlib.Cryptography and Games defined by explicit Games.Hopping import',
 'status':'NOT_RUN'})
(B/'overlap/static-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
print('WROTE 11 public-only templates: 4 proposed helpers + 7 original obligations; full frozen M4 map16 rows.')
