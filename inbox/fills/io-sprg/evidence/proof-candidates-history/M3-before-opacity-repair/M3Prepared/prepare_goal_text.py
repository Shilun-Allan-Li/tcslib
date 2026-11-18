from pathlib import Path
import json,re
p=Path('/private/tmp/io-sprg-proof-notes/M3Prepared/overlap');rows=json.loads((p/'probe-index.json').read_text())
P=['TCSlib.Cryptography.Games.Bridges.Experiments','TCSlib.Cryptography.OneWayFunctions.Basic','Mathlib.Data.Finset.Powerset','Lean.Elab.Tactic.LibrarySearch']
A=['Mathlib.Analysis.SpecificLimits.Normed','Mathlib.Analysis.Complex.Exponential','TCSlib.Complexity.Randomized.PolyExpr','Lean.Elab.Tactic.LibrarySearch']
N=['TCSlib.Cryptography.Foundations.Probability','Mathlib.Data.Nat.Basic','Lean.Elab.Tactic.LibrarySearch']
E=['TCSlib.Cryptography.Foundations.Probability','Mathlib.Data.Nat.Choose.Bounds','Mathlib.Analysis.Complex.Exponential','Lean.Elab.Tactic.LibrarySearch']
def put(name,goal,imports=P,family='M3-helper-core',note='Scalar/finite-law core after actual published owner readers; no owned declaration is imported.'):
 text='\n'.join('import '+x for x in imports)+'\n\nset_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n\nopen TCSlib.Cryptography\n\n'+goal+' := __PROBE_BODY__\n'
 assert text.count(':= __PROBE_BODY__')==1 and not re.search(r'\bby\b|Type\*|BigOperators|Obfuscation',text)
 f=p/'templates'/(name+'.lean.template');f.write_text(text)
 rows.append({'name':name,'family':family,'template':str(f.relative_to(p)),'imports':imports,'status':'UNRUN','abstraction':note})
put('bucket_count_upper_core','''example (m κ W : ℕ) (hW : 0 < W) :
    max 1 ((m * κ + W - 1) / W) ≤ m * κ + 1''',N)
put('bucket_count_lower_core','''example (m κ W : ℕ) (hW : 0 < W) :
    m * κ ≤ max 1 ((m * κ + W - 1) / W) * W''',N)
put('prefactor_eventually_le_two_pow_core','''example (B m : ℕ → ℕ) (q : Complexity.PolyExpr)
    (hm : ∀ κ, m κ ≤ q.eval κ) (hB : ∀ κ, B κ ≤ m κ * κ + 1) :
    ∃ κ₀, ∀ κ ≥ κ₀, (((κ + 1) * B κ + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ κ''',A,note='Actual composed output polynomial majorant and previously proved bucket-count upper bound are abstracted; coefficient retained through existing limit, no monic normalization helper.')
put('cond1_single_le_quarter_core','''example (cLoc m W n : ℕ) (hW : 0 < W) (hlog : 4 * cLoc ≤ Nat.log 2 n) :
    (cLoc : ℝ) * m / ((W : ℝ) * (m * Nat.log 2 n / W + 1)) ≤ (4 : ℝ)⁻¹''',N+['Mathlib.Data.Nat.Log'])
put('cond1_repetitions_fixed_index_core','''example {Secret Noise : Type} [Fintype Secret] [Nonempty Secret]
    [Fintype Noise] [Nonempty Noise] (κ : ℕ) (q : Noise → Prop)
    (h : uprob q ≤ (4 : ℝ)⁻¹) :
    uprob (fun reps : Fin κ → Secret × Noise => ∀ k, q (reps k).2) ≤ (4 : ℝ)⁻¹ ^ κ''',note='Entire index is FIXED before this probability; Secret/Noise are actual independent repetition coordinates. No unconditional independence after index averaging is assumed.')
put('cond1_all_fixed_index_core','''example {Seed Rep : Type} [Fintype Seed] [Nonempty Seed]
    [Fintype Rep] [Nonempty Rep] (κ : ℕ) (q : Rep → Prop)
    (h : uprob (fun reps : Fin κ → Rep => ∀ k, q (reps k)) ≤ (4 : ℝ)⁻¹ ^ κ) :
    uprob (fun d : Seed × (Fin κ → Rep) => ∀ k, q (d.2 k)) ≤ (4 : ℝ)⁻¹ ^ κ''',note='After sdSampFull pushforward/sdCore_draw readers, discard only the independent Boolean Seed, retaining the fixed-index tuple event.')
put('cond1_all_joint_core','''example {I X : Type} (idx : Games.ProbComp I) (law : I → Games.ProbComp X)
    (q : I → X → Prop) (κ : ℕ)
    (h : ∀ i, Games.ProbComp.prob (law i) (q i) ≤ (4 : ℝ)⁻¹ ^ κ) :
    Games.ProbComp.prob
      (idx.bind fun i => (fun x => (i, x)) <$> law i)
      (fun x => q x.1 x.2) ≤ (4 : ℝ)⁻¹ ^ κ''',note='idx is the ACTUAL possibly nonuniform index law, not a uniform I. Fixed-index estimate is the preceding helper conclusion.')
put('binomial_ratio_quarter_core','''example (N B r κ : ℕ) (hB : 0 < B) (hr : 0 < r)
    (hbase : 4 * Real.exp 1 * (N : ℝ) ≤ (B : ℝ) * r) (hκ : κ ≤ r) :
    (Nat.choose N r : ℝ) / (B : ℝ) ^ r ≤ (4 : ℝ)⁻¹ ^ κ''',E)
put('smallset_bucket_tail_quarter_core','''example {m B : ℕ} [NeZero B] (Γ κ : ℕ) (S : Finset (Fin m))
    (hκ : 12 ≤ κ) (hS : S.card ≤ Γ) (hΓ : Γ ≤ B) :
    uprob (fun φ : Fin m → Fin B => ∃ b : Fin B,
      κ < ((Finset.univ.filter (fun j => φ j = b)) ∩ S).card) ≤
      (B : ℝ) * (4 : ℝ)⁻¹ ^ κ''')
put('capacity_bucket_tail_quarter_core','''example (m B W κ : ℕ) [NeZero B] (hW : 0 < W) (hκ : 12 ≤ κ)
    (hround : m * κ ≤ B * W) :
    uprob (fun φ : Fin m → Fin B => ∃ b : Fin B,
      κ ^ 2 * W < (Finset.univ.filter (fun j => φ j = b)).card) ≤
      (B : ℝ) * (4 : ℝ)⁻¹ ^ κ''',note='cap expands exactly to kappa^2*W; hround is preceding exact bucket-count-lower helper, no noise asymptotic assumption.')
put('cond3_joint_le_quarter_pow_core','''example {G Mat D : Type} [Fintype G] [Nonempty G] [Fintype Mat] [Nonempty Mat]
    [Fintype D] [Nonempty D] (m B W κ : ℕ) [NeZero B]
    (hW : 0 < W) (hκ : 12 ≤ κ) (hround : m * κ ≤ B * W) :
    uprob (fun z : (G × ((Fin m → Fin B) × Mat)) × D =>
      ∃ b : Fin B, κ ^ 2 * W < (Finset.univ.filter (fun j => z.1.2.1 j = b)).card) ≤
      (B : ℝ) * (4 : ℝ)⁻¹ ^ κ''',note='Actual index DRAW plus matrix/full draw, after public pushforward uniform bridge. Only uniform Buck marginal used; never replace generator index by uniform G.Idx.')
put('cond2_sparse_joint_le_quarter_pow_core','''example {G Mat D : Type} [Fintype G] [Nonempty G] [Fintype Mat] [Nonempty Mat]
    [Fintype D] [Nonempty D] (m B Γ κ : ℕ) [NeZero B]
    (hκ : 12 ≤ κ) (hΓ : Γ ≤ B) (S : G × (Mat × D) → Finset (Fin m)) :
    uprob (fun z : (G × (Mat × D)) × (Fin m → Fin B) =>
      (∃ b : Fin B, κ < ((Finset.univ.filter (fun j => z.2 j = b)) ∩ S z.1).card) ∧
        (S z.1).card ≤ Γ) ≤ (B : ℝ) * (4 : ℝ)⁻¹ ^ κ''',note='Exact bucket-LAST section core after hunif/htransport. S depends on G DRAW/matrix/full draw and ignores bucket labels. No assumption that all S are small: smallness remains INSIDE the event.')
put('errProb_nonneg_core','''example {X : Type} (c : Games.ProbComp X) (err : X → Bool) :
    0 ≤ Games.ProbComp.prob c (fun x => err x = true)''',family='M3-frozen-original-core')
put('badSet_expect_le_core','''example (n m W p cLoc : ℕ) [NeZero W] [NeZero p]
    (vars : Fin m → Finset (Fin n)) (hLoc : ∀ j, (vars j).card ≤ cLoc) :
    Games.ProbComp.expect (Games.ProbComp.sample (Fin n → Fin W × ZMod p))
      (fun r => ((Finset.univ.filter (fun j : Fin m =>
        ((vars j) ∩ Finset.univ.filter (fun i : Fin n =>
          (((if (r i).1 = 0 then ((r i).2.val : ℤ) else 0) : ℤ) : ZMod p) ≠ 0)).Nonempty)).card
          : ℝ)) ≤ (cLoc : ℝ) * m / W''',P+['Mathlib.Data.ZMod.Basic'],family='M3-frozen-original-core',note='Literal BAD dependency/error intersection, after actual variable sets and scalar noise readers. Uniform selector/residue draw retained, including integer-lift cast. Locality is actual per-output vars-card bound.')
put('cond1_prob_le_core','''example {X : Type} (c : Games.ProbComp X) (badCount : X → ℕ)
    (cLoc m W Γ : ℕ) (hW : 0 < W)
    (hmean : Games.ProbComp.expect c (fun x => (badCount x : ℝ)) ≤
      (cLoc : ℝ) * m / W) :
    Games.ProbComp.prob c (fun x => Γ < badCount x) ≤
      (cLoc : ℝ) * m / ((W : ℝ) * (Γ + 1))''',family='M3-frozen-original-core',note='Actual preceding first-moment estimate abstracted; consume public Lamport Markov API rather than reproduce it. Strict Nat threshold Gamma+1 retained.')
put('errProb_le_decomposition_core','''example {X : Type} [Fintype X] [Nonempty X] (κ : ℕ)
    (flags : X → Fin κ → Bool) (C : X → Prop) (A B : X → Fin κ → Prop)
    (hflags : ∀ x k, flags x k = true ↔ ¬ A x k ∧ ¬ C x ∧ ¬ B x k) :
    uprob (fun x => ∀ k, flags x k = false) ≤
      uprob C + Finset.sum Finset.univ
        (fun k : Fin κ => uprob (fun x => B x k ∧ ¬ A x k)) +
      uprob (fun x => ∀ k, A x k)''',family='M3-frozen-original-core',note='After actual exact draw pushforward and reused proved firstGood_none_iff. hflags is actual oneFlag reader rewritten to three complement failure predicates, not an extra independence premise.')
put('claim42_core','''example (PP : ℕ → Type) (B : ℕ → ℕ)
    (err c3 c1 : (κ : ℕ) → PP κ → ℝ)
    (c2 : (κ : ℕ) → PP κ → Fin κ → ℝ)
    (hparts : ∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PP κ,
      err κ pp ≤ c3 κ pp + Finset.sum Finset.univ (c2 κ pp) + c1 κ pp ∧
      c3 κ pp ≤ (B κ : ℝ) * (4 : ℝ)⁻¹ ^ κ ∧
      (∀ k, c2 κ pp k ≤ (B κ : ℝ) * (4 : ℝ)⁻¹ ^ κ) ∧
      c1 κ pp ≤ (4 : ℝ)⁻¹ ^ κ)
    (hpoly : ∃ κ₀, ∀ κ ≥ κ₀,
      (((κ + 1) * B κ + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ κ) :
    ∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PP κ, err κ pp ≤ (2 : ℝ)⁻¹ ^ κ''',family='M3-frozen-original-core',note='Final actual event-bound arithmetic/quantifier core. Both preceding cutoffs are BEFORE every pp, preserving prime-uniform threshold order.')
put('cond2_hunif_control','''example {I D : Type} [Fintype I] [Nonempty I] [Fintype D] [Nonempty D]
    (event : I × D → Prop) :
    Games.ProbComp.prob
      ((Games.ProbComp.sample I).bind fun i =>
        (Games.ProbComp.sample D).bind fun d => pure (i, d)) event = uprob event''',family='M3-public-reuse-control',note='Exact public sequential-uniform-pair probability bridge required by hunif. Type0; a search hit must be reused, not rederived.')
assert len(rows)==23
(p/'probe-index.json').write_text(json.dumps(rows,indent=2)+'\n');(p/'names.txt').write_text('\n'.join(x['name'] for x in rows if x['family']!='M3-public-reuse-control')+'\n');(p/'control-names.txt').write_text('cond2_hunif_control\n')
print('22required original/helper goals +1public control; zero tactic blocks')
