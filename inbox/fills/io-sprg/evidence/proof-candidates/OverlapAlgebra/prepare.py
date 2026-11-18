"""Create zero-tactic-block isolated mathematical overlap templates. No Lean."""
from pathlib import Path
import csv,hashlib,json,re,shutil
base=Path('/private/tmp/io-sprg-proof-notes/OverlapAlgebra')
repo=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
old=Path('/private/tmp/io-sprg-proof-notes/AlgebraEvaluation')
rows=list(csv.DictReader((old/'inventory.tsv').open(),delimiter='\t'))
index=[]
Wpub='(Sum.elim\n      (fun _ : σ => (1 : ℕ)) (fun _ : τ => (0 : ℕ)))'
Wpriv='(Sum.elim\n      (fun _ : σ => (0 : ℕ)) (fun _ : τ => (1 : ℕ)))'
poly=['Mathlib.RingTheory.MvPolynomial.Homogeneous',
      'Mathlib.Data.Finset.Sort','Mathlib.Algebra.MvPolynomial.Eval',
      'Mathlib.Algebra.BigOperators.Ring.Finset']
polyeval=poly+['Mathlib.RingTheory.MvPolynomial.Basic',
               'Mathlib.Algebra.MvPolynomial.Variables','Mathlib.Algebra.BigOperators.Fin']
coeff='''    let c : Option (Fin n) → Fin (ell + 1) → MvPolynomial (σ ⊕ τ) R :=
      fun slot a => match slot with
      | none => if a.val = ell then 1 else 0
      | some i => if ha : a.val < ell then
          MvPolynomial.C (-A i ⟨a.val, ha⟩) else MvPolynomial.X (.inl (b i))
'''
half='''    let H : (Fin n →₀ ℕ) → ℕ → Bool → MvPolynomial (σ ⊕ τ) R :=
      fun h offset copy => ∑ α : Fin D → Fin (ell + 1),
        (∏ r : Fin D, c ((h.support.sort (· ≤ ·))[offset + r.val]?) (α r)) *
          MvPolynomial.X (.inr (T copy α))
'''

def add(name,imports,goal,kind,abstraction,apis):
 owner=next(r['module'] for r in rows if r['declaration']==name)
 row=next(r for r in rows if r['declaration']==name)
 imports=list(dict.fromkeys(imports))
 text=''.join('import '+m+'\n' for m in imports)
 text+='import Lean.Elab.Tactic.LibrarySearch\n\n'
 text+='set_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\n'
 text+='set_option autoImplicit false\n\nopen scoped BigOperators\n'
 if 'TCSlib.Cryptography.Games.OracleComp' in imports:
  text+='open TCSlib.Cryptography.Games\n'
 text+='\nnamespace IoSprgAlgebraOverlap\n\n'+goal.strip()+' := __PROBE_BODY__\n'
 text+='\nend IoSprgAlgebraOverlap\n'
 assert text.count('__PROBE_BODY__')==1
 assert not re.search(r':=\s*by\b',text)
 assert not re.search(r'\b(sorry|axiom)\b',text)
 dest=base/'templates'/(name+'.lean.template');dest.write_text(text)
 index.append({'name':name,'family':owner,'template':str(dest.relative_to(base)),
   'imports':imports,'source':('TCSlib/Cryptography/Obfuscation/StructuredSeed/'+
      owner+'.lean:'+row['source_line']) if row['source_line'].isdigit() else
      'proposed Params.G4_seed_allOutputs helper',
   'kind':kind,'abstraction':abstraction,'public_apis':apis,'status':'NOT_RUN',
   'sha256':hashlib.sha256(text.encode()).hexdigest()})

add('Internal.monomialSlot_two_halves_card_le',poly,'''
example {n : ℕ} (h : Fin n →₀ ℕ) (D : ℕ) :
    (Finset.univ.filter (fun r : Fin D =>
      ((h.support.sort (· ≤ ·))[r.val]?).isSome)).card +
    (Finset.univ.filter (fun r : Fin D =>
      ((h.support.sort (· ≤ ·))[D + r.val]?).isSome)).card ≤ h.support.card
''','FULL_EXPANSION','Literal sorted support getElem? in both half blocks; no slot wrapper.',
'isSome_getElem?; Finset.length_sort; card_image_of_injective; card_union_of_disjoint; card_le_card')

common='''example {σ τ R : Type*} [CommRing R] {n ell D : ℕ}
    (A : Fin n → Fin ell → R) (b : Fin n → σ)
    (T : Bool → (Fin D → Fin (ell + 1)) → τ)
    (h : Fin n →₀ ℕ) (offset : ℕ) (copy : Bool) :
'''
add('halfForm_pubDegree_le',poly,common+coeff+half+f'''    (H h offset copy).weightedTotalDegree {Wpub} ≤
      (Finset.univ.filter (fun r : Fin D =>
        ((h.support.sort (· ≤ ·))[offset + r.val]?).isSome)).card
''','FULL_EXPANSION','A,b,T abstract actual matrix/public/tensor coordinates; actual padded coefficient and tensor sum are literal.',
'AddMonoidAlgebra.supDegree_sum_le; supDegree_prod_le; weightedTotalDegree_X; isWeightedHomogeneous_C; Finset.sum_boole')
add('halfForm_privDegree_le',poly,common+coeff+half+f'''    (H h offset copy).weightedTotalDegree {Wpriv} ≤ 1
''','FULL_EXPANSION','Same literal half form; arbitrary coordinate maps preserve the actual shape.',
'AddMonoidAlgebra.supDegree_sum_le; supDegree_prod_le; isWeightedHomogeneous_X; isWeightedHomogeneous_C')

add('prgPoly_degrees',polyeval,'''
example {σ τ R : Type*} [CommRing R] {n ell D d : ℕ}
    (A : Fin n → Fin ell → R) (b : Fin n → σ)
    (T : Bool → (Fin D → Fin (ell + 1)) → τ)
    (p : MvPolynomial (Fin n) ℤ) (hd : p.totalDegree ≤ d) (copy : Bool) :
'''+coeff+half+f'''    let q := ∑ h ∈ p.support,
      MvPolynomial.C ((p.coeff h : ℤ) : R) * H h 0 copy * H h D false
    q.weightedTotalDegree {Wpub} ≤ d ∧
      q.weightedTotalDegree {Wpriv} ≤ 2
''','FULL_EXPANSION_STRONGER','Literal coefficient-weighted pair of half forms. Only total degree is needed for degree bounds; unused multilinearity omitted.',
'Finset.card_nsmul_le_sum; MvPolynomial.le_totalDegree; weighted degree sum/product bounds')

add('correctionPoly_degrees',poly,'''
example {σ τ R : Type*} [CommRing R] {rc t : ℕ}
    (position : Option (Fin rc × Fin rc))
    (U : Bool → Fin rc → Fin t → τ) (V : Fin t → Fin rc → τ) (copy : Bool) :
    let q : MvPolynomial (σ ⊕ τ) R := match position with
      | none => 0
      | some c => ∑ r : Fin t,
          MvPolynomial.X (.inr (U copy c.1 r)) * MvPolynomial.X (.inr (V r c.2))
'''+f'''    q.weightedTotalDegree {Wpub} = 0 ∧
      q.weightedTotalDegree {Wpriv} ≤ 2
''','FULL_EXPANSION','Optional grid position and private U/V coordinate maps abstract the actual selected bucket; both branches are retained.',
'weightedTotalDegree_zero; AddMonoidAlgebra.supDegree_sum_le; supDegree_mul_le; isWeightedHomogeneous_X')

add('G3_degrees',poly,f'''
example {{σ τ R : Type*}} [CommSemiring R] (q r : MvPolynomial (σ ⊕ τ) R) (d : ℕ)
    (hq : q.weightedTotalDegree {Wpub} ≤ d ∧
      q.weightedTotalDegree {Wpriv} ≤ 2)
    (hr : r.weightedTotalDegree {Wpub} = 0 ∧
      r.weightedTotalDegree {Wpriv} ≤ 2) :
    (q + r).weightedTotalDegree {Wpub} ≤ d ∧
      (q + r).weightedTotalDegree {Wpriv} ≤ 2
''','ACTUAL_PREMISE_COMPOSITION','q/r are the lifted PRG/correction; hq/hr are exactly their upstream bidegree facts. No G3 conclusion is assumed.',
'AddMonoidAlgebra.supDegree_add_le; max_le; Nat.zero_le')

add('G4_degrees',poly+['Mathlib.Algebra.MvPolynomial.Rename'],f'''
example {{σ τ σ' τ' R : Type*}} [CommSemiring R] {{κ d : ℕ}}
    (e : σ ≃ σ') (f : τ ≃ τ') (q : Fin κ → MvPolynomial (σ ⊕ τ) R)
    (hq : ∀ k, (q k).weightedTotalDegree {Wpub} ≤ d ∧
      (q k).weightedTotalDegree {Wpriv} ≤ 2) :
    let Q := MvPolynomial.rename (Sum.map e f) (∑ k : Fin κ, q k)
    Q.weightedTotalDegree
      (Sum.elim (fun _ : σ' => (1 : ℕ)) (fun _ : τ' => (0 : ℕ))) ≤ d ∧
    Q.weightedTotalDegree
      (Sum.elim (fun _ : σ' => (0 : ℕ)) (fun _ : τ' => (1 : ℕ))) ≤ 2
''','ACTUAL_PREMISE_COMPOSITION','Literal renamed sum; hq is exactly the per-instance G3 degree fact. Arbitrary groupwise equivalences cover the concrete public/private maps.',
'MvPolynomial.weightedTotalDegree_rename_of_injective; AddMonoidAlgebra.supDegree_sum_le')

half_eval_binders='''example {σ τ R : Type*} [CommRing R] {n ell D : ℕ}
    (A : Fin n → Fin ell → R) (b : Fin n → σ)
    (T : Bool → (Fin D → Fin (ell + 1)) → τ)
    (s : Fin ell → R) (x : Fin n → R) (z : σ ⊕ τ → R)
    (hpub : ∀ i, z (.inl (b i)) = (∑ a, A i a * s a) + x i)
    (htensor : ∀ α : Fin D → Fin (ell + 1),
      z (.inr (T false α)) =
        ∏ r : Fin D, if ha : (α r).val < ell then s ⟨(α r).val, ha⟩ else 1)
'''
add('halfForm_eval',polyeval,half_eval_binders+'''    (h : Fin n →₀ ℕ) (offset : ℕ) :
'''+coeff+half+'''    MvPolynomial.eval z (H h offset false) =
      ∏ r : Fin D, match (h.support.sort (· ≤ ·))[offset + r.val]? with
        | none => 1
        | some i => x i
''','FULL_EXPANSION','Matrix/secret/public/tensor assignment and coefficient/padding expressions are all explicit; dimensions including zero are arbitrary.',
'Fintype.prod_sum; Fin.sum_univ_castSucc; MvPolynomial.eval_sum/prod/C/X; sum_neg_distrib')

add('G1_eval',polyeval,half_eval_binders+'''    (p : MvPolynomial (Fin n) ℤ) (d : ℕ)
    (hml : p ∈ MvPolynomial.restrictDegree (Fin n) ℤ 1)
    (hdeg : p.totalDegree ≤ d) (hcut : d ≤ D + D) :
'''+coeff+half+'''    MvPolynomial.eval z
      (∑ h ∈ p.support,
        MvPolynomial.C ((p.coeff h : ℤ) : R) * H h 0 false * H h D false) =
      MvPolynomial.eval₂ (Int.castRingHom R) x p
''','FULL_EXPANSION','Actual integer representation becomes arbitrary p with the supplied multilinearity/degree premises; hcut is the existing ceil-half-degree arithmetic consequence.',
'MvPolynomial.mem_restrictDegree; le_totalDegree; eval₂_eq; Fin.prod_univ_add; prod_univ_eq_prod_range; List.prod_toFinset')

add('G3_eval_of_scaled',polyeval,'''
example {σ τ R ι ρ : Type*} [CommRing R] [Fintype ι] [Fintype ρ]
    (a : ι → MvPolynomial (σ ⊕ τ) R) (T : Bool → ι → τ)
    (U : Bool → ρ → τ) (V : ρ → τ) (z : σ ⊕ τ → R) (flag : R)
    (hT : ∀ i, z (.inr (T true i)) = flag * z (.inr (T false i)))
    (hU : ∀ r, z (.inr (U true r)) = flag * z (.inr (U false r))) :
    MvPolynomial.eval z
      ((∑ i, a i * MvPolynomial.X (.inr (T true i))) +
        ∑ r, MvPolynomial.X (.inr (U true r)) * MvPolynomial.X (.inr (V r))) =
      flag * MvPolynomial.eval z
        ((∑ i, a i * MvPolynomial.X (.inr (T false i))) +
          ∑ r, MvPolynomial.X (.inr (U false r)) * MvPolynomial.X (.inr (V r)))
''','STRUCTURAL_CORE','Flatten supported monomial/first-half tensor indices to finite i; a i is the unchanged coefficient product times second half. Optional-none corrections use empty rho. Actual hcopy restricts to hT/hU. Full nested expression deliberately replaced by its exact linear-scaling core.',
'MvPolynomial.eval_sum/mul/add/X; Finset.mul_sum; Finset.sum_congr; ring identities')

selection=['Mathlib.Data.List.FinRange','Mathlib.Data.List.OfFn']
add('firstGood_none_iff',selection,'''
example {κ : ℕ} (flags : Fin κ → Bool) :
    (List.finRange κ).find? flags = none ↔ ∀ k, flags k = false
''','FULL_EXPANSION','Literal increasing finite find?; no firstGood wrapper.',
'List.find?_eq_none; List.mem_finRange; Bool.eq_false_iff')
add('firstGood_some_flag',selection,'''
example {κ : ℕ} (flags : Fin κ → Bool) (k : Fin κ)
    (h : (List.finRange κ).find? flags = some k) : flags k = true
''','FULL_EXPANSION','Literal first-success search.', 'List.find?_some')
add('firstGood_some_minimal',selection,'''
example {κ : ℕ} (flags : Fin κ → Bool) (k : Fin κ)
    (h : (List.finRange κ).find? flags = some k) (q : Fin κ) (hq : q < k) :
    flags q = false
''','FULL_EXPANSION','Literal first-success search and exact earlier-index order.',
'List.ofFn_id; List.find?_ofFn_eq_some_of_injective; Bool.eq_false_iff')

pubimports=['Mathlib.Logic.Equiv.Basic','Mathlib.Algebra.Ring.Basic']
add('packSeed_public_block',pubimports,'''
example {κ n pubLen : ℕ} {R : Type*} [CommRing R]
    (e : ((Fin κ × Fin n) ⊕ Unit) ≃ Fin pubLen)
    (instances : Fin κ → Fin n → R) (first : Option (Fin κ))
    (k : Fin κ) (i : Fin n) :
    (fun j => match e.symm j with
      | .inl q => instances q.1 q.2
      | .inr _ => (first.isNone.toNat : R)) (e (.inl (k, i))) = instances k i
''','FULL_EXPANSION','Literal public packing function and arbitrary explicit equivalence.',
'Equiv.symm_apply_apply; Sum.elim_inl')
add('packSeed_error',pubimports,'''
example {κ n pubLen : ℕ} {R : Type*} [CommRing R]
    (e : ((Fin κ × Fin n) ⊕ Unit) ≃ Fin pubLen)
    (instances : Fin κ → Fin n → R) (first : Option (Fin κ)) :
    (fun j => match e.symm j with
      | .inl q => instances q.1 q.2
      | .inr _ => (first.isNone.toNat : R)) (e (.inr ())) =
        (first.isNone.toNat : R)
''','FULL_EXPANSION','Literal public packing at its final Unit coordinate.', 'Equiv.symm_apply_apply')

packpriv='''    (fun j => let q := e.symm j
      match q.2 with
      | .inl _ => if first = some q.1 then 1 else 0
      | .inr (.inl v) => instances q.1 v
      | .inr (.inr v) => (if first = some q.1 then 1 else 0) * instances q.1 v)
'''
privbind='''example {κ privLen : ℕ} {R S : Type*} [CommRing R]
    (e : (Fin κ × (Unit ⊕ (S ⊕ S))) ≃ Fin privLen)
    (instances : Fin κ → S → R) (first : Option (Fin κ)) (k : Fin κ)
'''
add('packSeed_flag',pubimports,privbind+'''    :
'''+packpriv+'''      (e (k, .inl ())) = if first = some k then 1 else 0
''','FULL_EXPANSION','Literal private packing including both seed copies; select the flag branch.',
'Equiv.symm_apply_apply')
add('packSeed_unscaled',pubimports,privbind+'''    (v : S) :
'''+packpriv+'''      (e (k, .inr (.inl v))) = instances k v
''','FULL_EXPANSION','Literal private packing; select the original seed copy.', 'Equiv.symm_apply_apply')
add('packSeed_scaled',pubimports,privbind+'''    (v : S) :
'''+packpriv+'''      (e (k, .inr (.inr v))) =
        (if first = some k then (1 : R) else 0) * instances k v
''','FULL_EXPANSION','Literal private packing; select the flag-times-seed copy.', 'Equiv.symm_apply_apply')

add('oneFlag_bounds',['Mathlib.Data.Finset.Card','Mathlib.Data.Fintype.Basic'],'''
example {m B : ℕ} (φ : Fin m → Fin B) (bad : Finset (Fin m)) (Γ rc t : ℕ)
    (h : decide (bad.card ≤ Γ ∧
      ¬ (∃ b : Fin B, rc ^ 2 < (Finset.univ.filter (fun j => φ j = b)).card) ∧
      ∀ b : Fin B,
        ((Finset.univ.filter (fun j => φ j = b)) ∩ bad).card ≤ t) = true) :
    bad.card ≤ Γ ∧
      ¬ (∃ b : Fin B, rc * rc < (Finset.univ.filter (fun j => φ j = b)).card) ∧
      ∀ b : Fin B,
        ((Finset.univ.filter (fun j => φ j = b)) ∩ bad).card ≤ t
''','FULL_EXPANSION','Literal decide conjunction, bucket filters, load cardinalities and squared capacity; BAD may be arbitrary because its construction is unused here.',
'of_decide_eq_true; pow_two; And.left; And.right')

corrimports=['Mathlib.Algebra.MvPolynomial.Variables','Mathlib.Data.Fintype.BigOperators']
corrbind='''example {n : ℕ} {R : Type*} [CommRing R] [DecidableEq R]
    (p : MvPolynomial (Fin n) ℤ) (σ : Fin n → Bool) (e : Fin n → R) (out : Bool)
    (hgood : ¬ (p.vars ∩ (Finset.univ.filter (fun i => e i ≠ 0))).Nonempty)
    (hrep : MvPolynomial.eval (fun i => ((σ i).toNat : ℤ)) p = (out.toNat : ℤ))
'''
add('corr_zero_of_not_bad',corrimports,corrbind+'''    :
    (out.toNat : R) - MvPolynomial.eval₂ (Int.castRingHom R)
      (fun i => ((σ i).toNat : R) + e i) p = 0
''','FULL_EXPANSION','Actual no-error-in-variable-set premise, integer Boolean representation equation, and correction difference; noise draw mechanism is irrelevant once e is fixed.',
'MvPolynomial.eval₂Hom_congr\'; eval₂_comp; map_natCast; sub_self')

src=(Path('/private/tmp/io-sprg-proof-notes/OverlapProbes/templates')/
     'sparse_reconstruct.lean.template').read_text()
goal=src.split('example ',1)[1].split(' := __PROBE_BODY__',1)[0]
add('oneSd_factors_mul',['Mathlib.Data.List.FinRange','Mathlib.Data.Matrix.Mul',
     'Mathlib.Data.Finset.Card'],'example '+goal,'STRUCTURAL_CORE_REUSED',
'Existing sparse_reconstruct probe verbatim: arbitrary matrix with its actual Nodup nonzero-entry list and capacity bound, explicit padded factors. Concrete bucket support and successful oneSd reader transport are not included. No sparseFactor or bucket owner is imported.',
'List.getElem?/Nodup; Matrix.mul_apply; Finset.sum_eq_single; existing OverlapProbes/sparse_reconstruct')

add('G1_eval_of_good',corrimports,corrbind+'''    {V : Type*} (q : MvPolynomial V R) (z : V → R)
    (hq : MvPolynomial.eval z q = MvPolynomial.eval₂ (Int.castRingHom R)
      (fun i => ((σ i).toNat : R) + e i) p) :
    MvPolynomial.eval z q = (out.toNat : R)
''','ACTUAL_PREMISE_COMPOSITION','hq is the upstream G1 tensor evaluation. The no-BAD and supplied integer representation premises are retained explicitly, rather than assuming zero correction or the target.',
'MvPolynomial.eval₂Hom_congr\'; eval₂_comp; Eq.trans')

add('correctionPoly_eval_oneSd',['Mathlib.Data.Matrix.Mul','Mathlib.Data.Fintype.BigOperators'],'''
example {m B rc t : ℕ} {R : Type*} [Semiring R]
    (φ : Fin m → Fin B) (pos : Fin m → Option (Fin rc × Fin rc))
    (corr : Fin m → R) (j : Fin m) (c : Fin rc × Fin rc)
    (hpos : pos j = some c)
    (hinj : ∀ i, φ i = φ j → pos i = pos j → i = j)
    (U : Matrix (Fin rc) (Fin t) R) (V : Matrix (Fin t) (Fin rc) R)
    (hfactor : U * V = fun u v => ∑ i : Fin m,
      if φ i = φ j ∧ pos i = some (u, v) then corr i else 0) :
    (∑ r : Fin t, U c.1 r * V r c.2) = corr j
''','ACTUAL_PREMISE_COMPOSITION','Actual successful factor product, existing/injective optional position, and literal bucket matrix are retained. The polynomial evaluation itself is a direct eval_sum/mul/X reader step omitted from this core.',
'Matrix.mul_apply; Finset.sum_eq_single; Option.some.inj; Prod.ext')

add('G2_eval_of_flag',['Mathlib.Algebra.MvPolynomial.Eval'],'''
example {V R : Type*} [CommRing R] (q c : MvPolynomial V R) (z : V → R) (a b : R)
    (hq : MvPolynomial.eval z q = a) (hc : MvPolynomial.eval z c = b - a) :
    MvPolynomial.eval z (q + c) = b
''','ACTUAL_PREMISE_COMPOSITION','a is erroneous evaluation, b is correct field bit. hq/hc are the actual upstream G1 and successful correction evaluations; the success flag is used only to obtain hc.',
'MvPolynomial.eval_add; add_sub_cancel_left; sub_add_cancel; ring identities')

add('G4_eval_sdCore',['Mathlib.Algebra.MvPolynomial.Rename',
    'Mathlib.Algebra.BigOperators.Fin','Mathlib.Data.List.FinRange'],'''
example {κ : ℕ} {V W R : Type*} [CommRing R]
    (e : V ≃ W) (z : W → R) (q : Fin κ → MvPolynomial V R)
    (flags : Fin κ → Bool) (value : Fin κ → R) (out : R)
    (hq : ∀ k, MvPolynomial.eval (z ∘ e) (q k) =
      (if (List.finRange κ).find? flags = some k then 1 else 0) * value k)
    (hgood : ∀ k, flags k = true → value k = out) :
    MvPolynomial.eval z (MvPolynomial.rename e (∑ k : Fin κ, q k)) =
      if ((List.finRange κ).find? flags).isNone then 0 else out
''','ACTUAL_PREMISE_COMPOSITION','Literal renamed sum, finite first-success selection, and selected-output value. hq is scaled G3 after the separately probed packing coordinates; hgood is successful G2. No positive kappa is added.',
'MvPolynomial.eval_rename; eval_sum; List.find?_some; Finset.sum_ite_eq; sum_eq_single')

oracle=['TCSlib.Cryptography.Games.OracleComp','Mathlib.Algebra.MvPolynomial.Eval']
seedbind='''{ι X σ τ R J : Type*} [CommRing R] (spec : OracleSpec ι)
    (seed : X → (σ → R) × (τ → R)) (err : X → Bool) (out : X → J → Bool)
    (Q : J → MvPolynomial (σ ⊕ τ) R)
'''
fieldpred='''fun x => ∀ j,
      MvPolynomial.eval (Sum.elim (seed x).1 (seed x).2) (Q j) =
        if err x then 0 else ((out x j).toNat : R)'''
add('G4_eval_eq',oracle,'example '+seedbind+'''    {D : Type*} (draw : OracleComp spec D) (core : D → X)
    (hcore : ∀ d j,
      MvPolynomial.eval (Sum.elim (seed (core d)).1 (seed (core d)).2) (Q j) =
        if err (core d) then 0 else ((out (core d) j).toNat : R)) :
    (core <$> draw).AllOutputs ('''+fieldpred+''')
''','ACTUAL_PREMISE_COMPOSITION','Uniform law is abstracted to arbitrary draw because support pushforward uses no uniformity. hcore is the actual deterministic G4 core equality. No sampler is constructed.',
'OracleComp.map_eq_bind; allOutputs_true; AllOutputs.bind; allOutputs_pure')

add("eval'_correct",oracle,'example '+seedbind.replace('[CommRing R]','[CommRing R] [Nontrivial R] [DecidableEq R]')+'''    (c : OracleComp spec X)
    (hfield : c.AllOutputs ('''+fieldpred+''')) :
    c.AllOutputs (fun x => ∀ j,
      decide (MvPolynomial.eval (Sum.elim (seed x).1 (seed x).2) (Q j) = 1) =
        if err x then false else out x j)
''','FULL_EXPANSION_WITH_ACTUAL_PREMISE','Eval prime-field equality test is literal; hfield is G4_eval_eq. Arbitrary nontrivial commutative ring is stronger than the actual prime field. Decidability supplied by classical in materialization.',
'OracleComp.AllOutputs.mono; Bool.toNat_true; Bool.toNat_false; zero_ne_one; decide_eq_true_eq')

add('Params.G4_seed_allOutputs',oracle,'example '+seedbind+'''    (c : OracleComp spec X)
    (E : ((σ → R) × (τ → R)) → J → Bool)
    (hfield : c.AllOutputs ('''+fieldpred+'''))
    (hbit : c.AllOutputs (fun x => ∀ j,
      E (seed x) j = if err x then false else out x j)) :
    (seed <$> c).AllOutputs (fun sd => ∀ j,
      ((E sd j).toNat : R) = MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j))
''','ACTUAL_PREMISE_COMPOSITION','Two actual full-law support facts, same c, and literal projection-map conclusion. No generic AllOutputs conjunction result is assumed or imported.',
'OracleComp.allOutputs_pure/query; AllOutputs.mono/bind; map_eq_bind')

add('jls_hasComplexity',oracle+['Mathlib.RingTheory.MvPolynomial.Homogeneous',
    'Mathlib.Data.ZMod.Basic'],'''
example {ι : Type*} (spec : OracleSpec ι) (Idx : ℕ → Type)
    (p pub priv out : ℕ → ℕ) (d : ℕ)
    (G : ∀ κ, Idx κ → Fin (out κ) →
      MvPolynomial (Fin (pub κ) ⊕ Fin (priv κ)) (ZMod (p κ)))
    (S : ∀ κ, Idx κ → OracleComp spec
      ((Fin (pub κ) → ZMod (p κ)) × (Fin (priv κ) → ZMod (p κ))))
    (E : ∀ κ, Idx κ →
      ((Fin (pub κ) → ZMod (p κ)) × (Fin (priv κ) → ZMod (p κ))) →
      Fin (out κ) → Bool)
    (hdeg : ∀ κ i j,
      (G κ i j).weightedTotalDegree
        (Sum.elim (fun _ : Fin (pub κ) => 1) (fun _ : Fin (priv κ) => 0)) ≤ d ∧
      (G κ i j).weightedTotalDegree
        (Sum.elim (fun _ : Fin (pub κ) => 0) (fun _ : Fin (priv κ) => 1)) ≤ 2)
    (hsupp : ∀ κ i, (S κ i).AllOutputs (fun sd => ∀ j,
      ((E κ i sd j).toNat : ZMod (p κ)) =
        MvPolynomial.eval (Sum.elim sd.1 sd.2) (G κ i j)))
    (κ : ℕ) (i : Idx κ) :
    ∃ Q : Fin (out κ) →
      MvPolynomial (Fin (pub κ) ⊕ Fin (priv κ)) (ZMod (p κ)),
      (∀ j, (Q j).weightedTotalDegree
        (Sum.elim (fun _ : Fin (pub κ) => 1) (fun _ : Fin (priv κ) => 0)) ≤ d ∧
        (Q j).weightedTotalDegree
          (Sum.elim (fun _ : Fin (pub κ) => 0) (fun _ : Fin (priv κ) => 1)) ≤ 2) ∧
      (S κ i).AllOutputs (fun sd => ∀ j,
        ((E κ i sd j).toNat : ZMod (p κ)) =
          MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j))
''','FULL_CONTRACT_EXPANSION_WITH_ACTUAL_PREMISES','Raw.HasComplexity expanded completely after record readers: G is literal G4, hdeg and hsupp are existing degree and proposed seed-support facts. Every kappa/index remains quantified; no sampler or machine is supplied by the probe.',
'Exists.intro; And.intro; public existential witness composition')

assert len(index)==29
(base/'probe-index.json').write_text(json.dumps(index,indent=2)+'\n')
(base/'names.txt').write_text('\n'.join(r['name']for r in index)+'\n')
with (base/'mapping.tsv').open('w')as f:
 w=csv.writer(f,delimiter='\t');w.writerow(['name','kind','source','abstraction','public_apis','status'])
 for r in index:w.writerow([r[k]for k in ('name','kind','source','abstraction','public_apis','status')])
shutil.copyfile('/private/tmp/io-sprg-proof-notes/OverlapEncoding/materialize.py',base/'materialize.py')
checks=[]
for r in index:
 text=(base/r['template']).read_text()
 checks.append({'name':r['name'],'markers':text.count('__PROBE_BODY__'),
   'tactic_blocks':len(re.findall(r':=\s*by\b',text)),
   'max_width':max(map(len,text.splitlines())),'lines':len(text.splitlines())})
 assert checks[-1]['markers']==1 and checks[-1]['tactic_blocks']==0
(base/'static-checks.json').write_text(json.dumps({'status':'STATIC_ONLY_NOT_RUN',
   'checks':checks},indent=2)+'\n')
(base/'source-binding.json').write_text(json.dumps({
 str(repo/'TCSlib/Cryptography/Obfuscation/StructuredSeed'/name):
 hashlib.sha256((repo/'TCSlib/Cryptography/Obfuscation/StructuredSeed'/name).read_bytes()).hexdigest()
 for name in ('Polys.lean','Correctness.lean','Samplers.lean','Defs.lean','Degree.lean')},indent=2)+'\n')
print('29 zero-tactic-block goal templates written. No Lean or materializer executed.')
