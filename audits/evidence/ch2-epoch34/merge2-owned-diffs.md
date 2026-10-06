# Merge #2 owned-file evidence (finding 2)

First-parent diffs of merge commit `53072100` (bringing `f70c57c2`) on the two
owned files it touched, with git blob identities on both sides. The before
side is `5dc0881a` (= the A5 brief tip, the last pre-merge state of these
files, identical to their state at the 4A-5 integration); the after side is
the merge result, byte-identical to the current HEAD state audited by the
round-2 closure program.

## TCSlib/Complexity/ClassNP/SAT.lean

- before blob (git SHA-1): `d32714839d08b08412faefbef1f7d5c0fa5417e5`
- after blob (git SHA-1): `75cacb8164d2054dc4ae9f4358ed0df0ad6ce96d` (= HEAD)

```diff
diff --git a/TCSlib/Complexity/ClassNP/SAT.lean b/TCSlib/Complexity/ClassNP/SAT.lean
index d3271483..75cacb81 100644
--- a/TCSlib/Complexity/ClassNP/SAT.lean
+++ b/TCSlib/Complexity/ClassNP/SAT.lean
@@ -70,6 +70,44 @@ namespace Complexity
 open Std.Sat (CNF)
 open Turing
 
+/-! Local names for the shared polynomial-time toolkit (`ClassNP/PolyTimePairing.lean`,
+`TuringMachine/Composition.lean`), kept so this file's proofs can keep using its
+historical `sat_*` names. -/
+
+/-- A function computed in linear time is polynomial-time computable
+(`polyTimeComputable_of_linear`). -/
+private lemma sat_pt_linear (f : List Bool → List Bool)
+    (h : ∃ (M : FinTM Bool) (C : ℕ),
+      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f :=
+  polyTimeComputable_of_linear h
+
+/-- A fixed word is polynomial-time computable (`polyTimeComputable_const`). -/
+private lemma sat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) :=
+  polyTimeComputable_const w
+
+/-- Polynomial-time branching on a polynomial-time bit (`polyTimeComputable_ite`). -/
+private lemma sat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
+    (hp : PolyTimeComputable (fun x => [p x]))
+    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
+    PolyTimeComputable (fun x => if p x then f x else g x) :=
+  polyTimeComputable_ite hp hf hg
+
+/-- The conjunction of two polynomial-time bits is polynomial-time
+(`polyTimeComputable_and`). -/
+private lemma sat_pt_and {p q : List Bool → Bool}
+    (hp : PolyTimeComputable (fun x => [p x]))
+    (hq : PolyTimeComputable (fun x => [q x])) :
+    PolyTimeComputable (fun x => [p x && q x]) :=
+  polyTimeComputable_and hp hq
+
+/-- Composition of a function machine with a machine correct on its image
+(`FinTM.exists_comp_on_image`). -/
+private lemma sat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
+    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
+    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
+    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) :=
+  FinTM.exists_comp_on_image M U f g T₁ T₂ hM hU
+
 /-- **The language `SAT`** [AB09, §2.3.1]: binary strings whose decoded CNF
 formula is satisfiable. Decoding is total ([AB09, footnote 3]), with the empty —
 satisfiable — formula as fallback, so every non-well-formed string is in `SAT`
@@ -981,79 +1019,6 @@ private lemma satEval_computes : ∃ (E : FinTM Bool) (A : ℕ),
   simp only [Nat.add_mul]
   omega
 
-/-- Compose a computed request with a machine proved only on that request image.
-The budget is measured at the original input length, as in the audited TMSAT construction. -/
-private lemma sat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
-    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
-    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
-    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
-  refine ⟨FinTM.bufferedCompTM M U, ?_⟩
-  intro x
-  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
-    FinTM.bufferedComp_start M U x (f x) (T₁ x.length) (hM x)
-  have hlen : (f x).length ≤ T₁ x.length := by
-    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
-    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
-  obtain ⟨b, _, hr⟩ := FinTM.bufferedSecondCfg_run M U (U.tm.initCfg (f x)) true
-    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ x.length)
-  have hu := (FinTM.computesInTime_iff _ _ _ _).mp (hU x)
-  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a + T₂ x.length) := by
-    apply (FinTM.computesInTime_iff _ _ _ _).mpr
-    rw [MultiTapeTM.runFrom_add, hstart, hr]
-    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
-  exact hbase.mono (by dsimp only; omega)
-
-/-- Linear-time catalog contracts are instances of the polynomial calculus. -/
-private lemma sat_pt_linear (f : List Bool → List Bool)
-    (h : ∃ (M : FinTM Bool) (C : ℕ),
-      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f := by
-  obtain ⟨M, C, hM⟩ := h
-  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩
-
-/-- A fixed word is emitted from finite control. -/
-private lemma sat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) := by
-  exact sat_pt_linear _ (FinTM.computesFunInTime_const w)
-
-/-- Polynomial-time branches on the original input, using W3's captured
-single-bit decision. All three budgets fit their maximum degree.
-
-**Proof sketch.** Use the audited conditional constructor on the three witnessing machines. Bound each
-monomial by the common maximum exponent and absorb the constructor overhead into one
-coefficient. -/
-private lemma sat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
-    (hp : PolyTimeComputable (fun x => [p x]))
-    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
-    PolyTimeComputable (fun x => if p x then f x else g x) := by
-  obtain ⟨P, A, a, hP⟩ := hp
-  obtain ⟨F, B, b, hF⟩ := hf
-  obtain ⟨G, C, c, hG⟩ := hg
-  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hP hF hG
-  let e := max a (max b c)
-  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
-  have ha := Nat.mul_le_mul_left A
-    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show a ≤ e by exact Nat.le_max_left _ _))
-  have hb := Nat.mul_le_mul_left B
-    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show b ≤ e by omega))
-  have hc := Nat.mul_le_mul_left C
-    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show c ≤ e by omega))
-  have h1 : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
-  simp only [Nat.succ_eq_add_one] at ha hb hc
-  calc
-    _ ≤ K * ((A + B + C + 1) * (x.length + 1) ^ e) :=
-      Nat.mul_le_mul_left K (by simp only [Nat.add_mul, Nat.one_mul]; omega)
-    _ = _ := by ring
-
-
-/-- Short-circuit conjunction preserves the order of two polynomial tests. -/
-private lemma sat_pt_and {p q : List Bool → Bool}
-    (hp : PolyTimeComputable (fun x => [p x]))
-    (hq : PolyTimeComputable (fun x => [q x])) :
-    PolyTimeComputable (fun x => [p x && q x]) := by
-  have h := sat_pt_cond hp hq (sat_pt_const [false])
-  convert h using 1
-  funext x
-  cases p x <;> rfl
-
 /-- The catalog split emits an encoded pair, or an empty failure result. -/
 private def satSplit (z : List Bool) : List Bool :=
   match solveSplit 1 1 z.length with
@@ -1141,11 +1106,11 @@ private lemma sat_pipeline_poly :
   obtain ⟨M, A, hM⟩ := FinTM.computesFunInTime_splitSolve 1 1
   have hs : PolyTimeComputable satSplit := ⟨M, A, 3, hM⟩
   have hv : PolyTimeComputable (fun z => [satSplitValid z]) :=
-    (sat_pt_linear _ FinTM.computesFunInTime_pairValid).comp hs
+    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairValid).comp hs
   have hx : PolyTimeComputable satInstance :=
-    (sat_pt_linear _ FinTM.computesFunInTime_pairFst).comp hs
+    (polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst).comp hs
   have hp : PolyTimeComputable (fun z => [satSyntax (satInstance z)]) := satSyntax_poly.comp hx
-  exact ⟨hv, hx, hp, sat_pt_cond (sat_pt_and hv hp) hs (sat_pt_const _)⟩
+  exact ⟨hv, hx, hp, polyTimeComputable_ite (polyTimeComputable_and hv hp) hs (polyTimeComputable_const _)⟩
 
 /-- The evaluator is polynomial on all safe requests.
 
@@ -1164,7 +1129,7 @@ private lemma satSafeValue_poly : PolyTimeComputable (fun z => [satSafeValue z])
       have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM z)).2
       simpa only [hout] using M.tm.output_length_le z (C * (z.length + 1) ^ e)
     exact h.mono (Nat.mul_le_mul_left A (by omega))
-  obtain ⟨N, hN⟩ := sat_comp_on_image M E satSafe (fun z => [satSafeValue z])
+  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M E satSafe (fun z => [satSafeValue z])
     (fun n => C * (n + 1) ^ e) (fun n => A * (C * (n + 1) ^ e + 1)) hM heval
   refine ⟨N, 2 * C + A * (C + 1) + 2, e, fun z => (hN z).mono ?_⟩
   have hp : 1 ≤ (z.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
@@ -1177,7 +1142,7 @@ private lemma satSafeValue_poly : PolyTimeComputable (fun z => [satSafeValue z])
 /-- The SAT verifier rejects failed splits and otherwise uses the safe
 evaluation pipeline. Failed parses take its accepting fallback branch. -/
 private lemma satVerdict_false_poly : PolyTimeComputable (fun z => [satVerdict false z]) := by
-  have h := sat_pt_cond sat_pipeline_poly.1 satSafeValue_poly (sat_pt_const [false])
+  have h := polyTimeComputable_ite sat_pipeline_poly.1 satSafeValue_poly (polyTimeComputable_const [false])
   convert h using 1
   funext z
   cases hs : solveSplit 1 1 z.length with
@@ -1317,9 +1282,9 @@ only successfully parsed inputs reach the width scan. -/
 private lemma satVerdict_true_poly : PolyTimeComputable (fun z => [satVerdict true z]) := by
   have hw : PolyTimeComputable (fun z => [satWidthScan (satInstance z)]) :=
     satWidthScan_poly.comp sat_pipeline_poly.2.1
-  have hsem := sat_pt_and hw satSafeValue_poly
-  have hparse := sat_pt_cond sat_pipeline_poly.2.2.1 hsem (sat_pt_const [true])
-  have h := sat_pt_cond sat_pipeline_poly.1 hparse (sat_pt_const [false])
+  have hsem := polyTimeComputable_and hw satSafeValue_poly
+  have hparse := polyTimeComputable_ite sat_pipeline_poly.2.2.1 hsem (polyTimeComputable_const [true])
+  have h := polyTimeComputable_ite sat_pipeline_poly.1 hparse (polyTimeComputable_const [false])
   convert h using 1
   funext z
   cases hs : solveSplit 1 1 z.length with
```

## TCSlib/Complexity/ClassNP/EXP.lean

- before blob (git SHA-1): `ccf0254ac26c7edb12ab11eef6c1fb69b7c57ebd`
- after blob (git SHA-1): `fb8ee4382039df80004916680f0c78bc2dc3c65c` (= HEAD)

```diff
diff --git a/TCSlib/Complexity/ClassNP/EXP.lean b/TCSlib/Complexity/ClassNP/EXP.lean
index ccf0254a..fb8ee438 100644
--- a/TCSlib/Complexity/ClassNP/EXP.lean
+++ b/TCSlib/Complexity/ClassNP/EXP.lean
@@ -58,7 +58,7 @@ declarations in all — was removed under the epoch-2 gate's binding
 live/dead inventory (`audits/ch2-epoch2-resolutions.md`): the
 continuation's `exists_loopCfgTM` route replaced it, and the auditor's
 kernel walk confirmed it absent from every final target closure. The
-live checkpoint route `enumLoop_run` (consumed by `enumDecider`) is
+live checkpoint route `enumLoop_run` (consumed by `exists_proj_decider`) is
 retained unchanged.
 -/
 
@@ -117,8 +117,9 @@ private def enumInc : List Bool → Option (List Bool)
   | false :: bs => some (true :: bs)
   | true :: bs => (enumInc bs).map (false :: ·)
 
-/-- A width-`w` little-endian representation of the low `w` bits of `i`. -/
-private def enumWord : ℕ → ℕ → List Bool
+/-- **The width-`w` little-endian binary word** of `i`: its low `w` bits, least
+significant first (high zeros kept). -/
+def enumWord : ℕ → ℕ → List Bool
   | 0, _ => []
   | w + 1, i => decide (i % 2 = 1) :: enumWord w (i / 2)
 
@@ -1263,9 +1264,9 @@ private lemma enumCont_round_seam (MV : FinTM Bool) (x s : List Bool) (phase : B
 /-- The prepared verifier call accepts the exact assembled input `x ++ s`.
 Its bound includes assembly, the buffer rewind, and the verifier's actual
 polynomial budget on that input. -/
-private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
-    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
-    ∃ t ≤ a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4,
+private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (Tv : ℕ → ℕ)
+    (hV : MV.DecidesInTime V Tv) (x s : List Bool) :
+    ∃ t ≤ Tv (x.length + s.length) + 2 * (x.length + s.length) + 4,
       ((bufferedCompTM enumCont_concatTM MV).tm.runFrom
         (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
           (stateWord (bufferedCompTM enumCont_concatTM MV).k s)) t).state = none ∧
@@ -1276,7 +1277,7 @@ private lemma enumCont_verifier_call (MV : FinTM Bool) (V : Language Bool) (a d
   obtain ⟨t, ht, hh, ho⟩ := enumCont_prepared_comp enumCont_concatTM MV
     (Cfg.ofWords (input := x) false (fun _ => s)) (x ++ s)
     [MultiTapeTM.indicator V (x ++ s)] (x.length + s.length + 2)
-    (a * ((x ++ s).length + 1) ^ d)
+    (Tv (x ++ s).length)
     (by rw [enumCont_concat_run]; rfl) (by rw [enumCont_concat_run]; rfl) (hV (x ++ s))
   rw [enumCont_round_seam MV x s false] at hh ho
   simp only [List.length_append] at ht
@@ -1325,17 +1326,17 @@ private lemma enumCont_return_run {k : ℕ} {S H : Type} {x : List Bool}
 repeatable call: the candidate is retained, all other original source work
 is restored to blank, and the sole verdict is held on the capture tape.
 The concrete body still has to dispatch, clear that verdict, and increment. -/
-private lemma enumCont_clean_verifier (MV : FinTM Bool) (V : Language Bool) (a d : ℕ)
-    (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) (x s : List Bool) :
+private lemma enumCont_clean_verifier (MV : FinTM Bool) (V : Language Bool) (Tv : ℕ → ℕ)
+    (hV : MV.DecidesInTime V Tv) (x s : List Bool) :
     let Q := bufferedCompTM enumCont_concatTM MV
     let c₀ := Cfg.ofWords (input := x) Q.tm.q₀ (stateWord Q.k s)
-    ∃ t ≤ 3 * (a * (x.length + s.length + 1) ^ d + 2 * (x.length + s.length) + 4) +
+    ∃ t ≤ 3 * (Tv (x.length + s.length) + 2 * (x.length + s.length) + 4) +
         x.length + 9,
       (enumCont_cleanTM Q).tm.runFrom
         (captureCfg Sum.inl (.inr (.inl 0)) [] [] (enumCont_logCfg c₀ [])) t =
         enumCont_cleanCfg Q c₀ [MultiTapeTM.indicator V (x ++ s)] none 1 0 := by
   dsimp only
-  obtain ⟨t, ht, hh, ho⟩ := enumCont_verifier_call MV V a d hV x s
+  obtain ⟨t, ht, hh, ho⟩ := enumCont_verifier_call MV V Tv hV x s
   obtain ⟨r, hr, he⟩ := enumCont_clean_complete (bufferedCompTM enumCont_concatTM MV)
     (Cfg.ofWords (input := x) (bufferedCompTM enumCont_concatTM MV).tm.q₀
       (stateWord (bufferedCompTM enumCont_concatTM MV).k s))
@@ -2222,31 +2223,6 @@ private lemma enumCont_lift_init (M B : FinTM Bool) (hk : M.k ≤ B.k)
   rw [hh]
   rfl
 
-/-- One input-independent polynomial bounds both body phases. The degree
-dominates the verifier degree, unary-generator degree, and linear scans;
-the coefficient absorbs every fixed administrative transition. -/
-private lemma enumCont_common_bound (a d f c j n w : ℕ) :
-    let P := (n + w + 1) ^ (d + c + 2)
-    let A := 3 * a + 3 * f + 3 * j + 60
-    3 * (f * (n + 1) ^ (c + 1)) + n + 3 * w + 10 ≤ A * P ∧
-      3 * (a * (n + w + 1) ^ d + 2 * (n + w) + 4) +
-        3 * ((j + 3) * (w + 1)) + 2 * n + 3 * w + 22 ≤ A * P := by
-  dsimp only
-  let P := (n + w + 1) ^ (d + c + 2)
-  have hn : n + w + 1 ≤ P := by
-    calc n + w + 1 = (n + w + 1) ^ 1 := by simp
-      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
-  have hd : (n + w + 1) ^ d ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
-  have hf : (n + 1) ^ (c + 1) ≤ P :=
-    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
-  have ha' := Nat.mul_le_mul_left a hd
-  have hf' := Nat.mul_le_mul_left f hf
-  have hj' := Nat.mul_le_mul_left (j + 3) (show w + 1 ≤ P by omega)
-  change _ ≤ (3 * a + 3 * f + 3 * j + 60) * P ∧
-    _ ≤ (3 * a + 3 * f + 3 * j + 60) * P
-  simp only [Nat.add_mul, Nat.mul_assoc] at hj' ⊢
-  omega
-
 /-- A concrete body with polynomial startup and exact seam restoration gives
 the frozen enumerator configuration contract by the audited loop export.
 This lemma is conditional only on the two explicit body obligations below.
@@ -2256,15 +2232,15 @@ the common coefficient and degree to cover both fuel and body. Instantiate
 The terminal is `(2^w-1)+1=2^w`; on candidate indices use `enumCont_orbit`.
 Finally absorb the export's additive one using `1 ≤ (n+w+1)^D`, exactly as
 in infrastructure round 3, item 5. All constants are fixed before the input. -/
-private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
+private lemma enumCont_from_body (C c : ℕ) (G : ℕ → ℕ) (V : Language Bool)
     (body : FinTM Bool) (anchor : body.State)
     (hstart : ∀ x : List Bool,
-      ∃ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D,
+      ∃ t ≤ G x.length,
         (∀ t' < t, (body.tm.runFrom (body.tm.initCfg x) t').state ≠ some anchor) ∧
         body.tm.runFrom (body.tm.initCfg x) t =
           Cfg.ofWords anchor (stateWord body.k (List.replicate (C * (x.length + 1) ^ c) false)))
     (hround : ∀ (x s : List Bool), s.length = C * (x.length + 1) ^ c →
-      ∃ t, 0 < t ∧ t ≤ A * (x.length + C * (x.length + 1) ^ c + 1) ^ D ∧
+      ∃ t, 0 < t ∧ t ≤ G x.length ∧
         (∀ t', 0 < t' → t' < t →
           (body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t').state
             ≠ some anchor) ∧
@@ -2274,32 +2250,28 @@ private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
         else
           body.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord body.k s)) t =
             Cfg.ofWords anchor (stateWord body.k ((incFixed s).getD s))) :
-    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
+    ∃ (b : ℕ) (E : FinTM Bool), ∀ x : List Bool,
       ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
-        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+        startup ≤ b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ∧
         E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
         ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
-          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+          t ≤ b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ∧
           if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
             (E.tm.runFrom (cfg i) t).state = none ∧
               (E.tm.runFrom (cfg i) t).output = [true]
           else E.tm.runFrom (cfg i) t = cfg (i + 1) := by
   obtain ⟨F, f, hF⟩ := computesFunInTime_polyUnary C c
-  let T := fun n => (A + f) * (n + C * (n + 1) ^ c + 1) ^ (D + c + 1)
-  have hbody (n : ℕ) : A * (n + C * (n + 1) ^ c + 1) ^ D ≤ T n := by
-    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
+  let T := fun n => G n + f * (n + 1) ^ (c + 1)
+  have hbody (n : ℕ) : G n ≤ T n := Nat.le_add_right _ _
   have hfuel : F.ComputesFunInTime
       (fun x => Nat.bits (2 ^ (C * (x.length + 1) ^ c) - 1)) T := by
     intro x
     dsimp only
     rw [enumCont_fuel_bits]
     apply (hF x).mono
-    exact Nat.mul_le_mul (by omega)
-      ((Nat.pow_le_pow_left (by omega : x.length + 1 ≤
-        x.length + C * (x.length + 1) ^ c + 1) (c + 1)).trans
-        (Nat.pow_le_pow_right (by omega) (by omega)))
+    exact Nat.le_add_left _ _
   obtain ⟨E, K, hE⟩ := exists_loopCfgTM body F anchor
     (fun x s => s.length = C * (x.length + 1) ^ c)
     (fun _ s => (incFixed s).getD s)
@@ -2316,51 +2288,50 @@ private lemma enumCont_from_body (C c A D : ℕ) (V : Language Bool)
       intro x s hs
       obtain ⟨t, htpos, ht, hi, hh⟩ := hround x s hs
       exact ⟨t, htpos, ht.trans (hbody x.length), hi, hh⟩)
-  refine ⟨K * (A + f + 1), D + c + 1, E, fun x => ?_⟩
+  refine ⟨K * (f + 1), E, fun x => ?_⟩
   obtain ⟨cfg, startup, ht, hi, _, hend, hout, hr⟩ := hE x
   have hone : 1 ≤ 2 ^ (C * (x.length + 1) ^ c) := Nat.one_le_two_pow
   have hterminal : 2 ^ (C * (x.length + 1) ^ c) - 1 + 1 =
       2 ^ (C * (x.length + 1) ^ c) := Nat.sub_add_cancel hone
   rw [hterminal] at hend hout
-  have hbudget : K * (T x.length + 1) ≤ K * (A + f + 1) *
-      (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) := by
-    have hp : 1 ≤ (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1) :=
-      Nat.one_le_pow _ _ (by omega)
-    calc K * (T x.length + 1) ≤ K * (T x.length +
-        (x.length + C * (x.length + 1) ^ c + 1) ^ (D + c + 1)) :=
-          Nat.mul_le_mul_left K (Nat.add_le_add_left hp _)
-      _ = _ := by dsimp [T]; ring
+  have hbudget : K * (T x.length + 1) ≤ K * (f + 1) *
+      (G x.length + (x.length + 1) ^ (c + 1) + 1) := by
+    rw [Nat.mul_assoc]
+    apply Nat.mul_le_mul_left K
+    dsimp only [T]
+    have e : (f + 1) * (G x.length + (x.length + 1) ^ (c + 1) + 1) =
+        f * G x.length + f * (x.length + 1) ^ (c + 1) + f + G x.length +
+          (x.length + 1) ^ (c + 1) + 1 := by ring
+    rw [e]
+    omega
   refine ⟨cfg, startup, ht.trans hbudget, hi, hend, hout, ?_⟩
   intro i hi
   obtain ⟨t, ht, hh⟩ := hr i (by omega)
   rw [enumCont_orbit _ i hi] at hh
   exact ⟨t, ht.trans hbudget, hh⟩
 
-/-- **Continuation frontier; admitted in this partial delivery.** There is one
-uniform finite machine with a polynomial startup and a polynomially bounded
-accept-or-advance segment for each exact-width candidate. The configuration
-after the last rejected candidate is a halted singleton rejection.
-
-**Proof sketch / remaining construction.** Evaluate `C(n+1)^c` and construct
-the all-false candidate while retaining the instance; assemble `x ++ u` on
-the virtual input buffer. Use `enumCapture_returns` for the captured call.
-On rejection, clear the bounded visited work region, reset all source and
-buffer heads and the captured bit, and use `enumCarry_correct` to increment.
-Its `enumBump_inc`/`enumInc_word` specification supplies the next rank or the
-overflow signal. Emit the single final answer only on acceptance or overflow.
-Prove the startup and per-round configuration equalities below with a uniform
-polynomial budget. These machine assembly and reset obligations are NOT
-discharged by the counter, capture, and abstract loop lemmas alone. -/
-private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
-    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
-    ∃ (b e : ℕ) (E : FinTM Bool), ∀ x : List Bool,
+/-- **The enumerator's configuration contract** (generalized verifier budget): one
+uniform finite machine, from its initial configuration, reaches the round of the first
+candidate within `b (Tv(n + w) + (n + w + 1)^{c+1})` steps (`w = C(n+1)^c`); each round
+either accepts (when `x ++ u ∈ V`) or advances to the next candidate within the same
+budget; after the last candidate it halts rejecting.
+
+**Proof sketch.** Instantiate `enumCont_from_body` with the body of the original
+construction (unary width generator, captured verifier call on `x ++ u`, reversible
+cleanup, fixed-width increment), bounding its startup and round costs by
+`A (n + w + 1)^{c+1} + 3 Tv(n + w)`. -/
+private theorem enumMachine_contracts (C c : ℕ) (V : Language Bool) (Tv : ℕ → ℕ)
+    (MV : FinTM Bool) (hV : MV.DecidesInTime V Tv) :
+    ∃ (b : ℕ) (E : FinTM Bool), ∀ x : List Bool,
       ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ),
-        startup ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+        startup ≤ b * (Tv (x.length + C * (x.length + 1) ^ c) +
+          (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) ∧
         E.tm.runFrom (E.tm.initCfg x) startup = cfg 0 ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).state = none ∧
         (cfg (2 ^ (C * (x.length + 1) ^ c))).output = [false] ∧
         ∀ i, i < 2 ^ (C * (x.length + 1) ^ c) → ∃ t,
-          t ≤ b * (x.length + C * (x.length + 1) ^ c + 1) ^ e ∧
+          t ≤ b * (Tv (x.length + C * (x.length + 1) ^ c) +
+            (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) ∧
           if MultiTapeTM.indicator V (x ++ enumWord (C * (x.length + 1) ^ c) i) then
             (E.tm.runFrom (cfg i) t).state = none ∧
               (E.tm.runFrom (cfg i) t).output = [true]
@@ -2378,32 +2349,73 @@ private theorem enumMachine_contracts (C c a d : ℕ) (V : Language Bool)
   have hRB : R.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
   have hUB : U.k ≤ B.k := by dsimp [B, enumCont_sources]; omega
   have hB : 0 < B.k := lt_of_lt_of_le hQ hQB
-  apply enumCont_from_body C c (3 * a + 3 * f + 3 * j + 60) (d + c + 2) V
-    (enumCont_bodyTM B qv qi false) (.inr 0)
-  · intro x
-    have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
-      (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
-      (f * (x.length + 1) ^ (c + 1)) (hU x)
-    obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
-      (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
-    exact ⟨t, ht.trans (enumCont_common_bound a d f c j x.length
-      (C * (x.length + 1) ^ c)).1, hn, he⟩
-  · intro x s hs
-    obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V a d hV x s
-    obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
-    have hv := enumCont_lift_call Q B hQ hQB Sum.inl
-      (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
-    have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
-      (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
-    obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
-      (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
-    refine ⟨t, htpos, ?_, hn, he⟩
-    have hb := (enumCont_common_bound a d f c j x.length s.length).2
-    rw [hs] at hb
-    apply le_trans (show t ≤ 3 * (a * (x.length + s.length + 1) ^ d +
-      2 * (x.length + s.length) + 4) + 3 * ((j + 3) * (s.length + 1)) +
-      2 * x.length + 3 * s.length + 22 by omega)
-    simpa only [hs] using hb
+  let A := 3 * f + 3 * j + 60
+  let P := fun n => (n + C * (n + 1) ^ c + 1) ^ (c + 1)
+  let G := fun n => A * P n + 3 * Tv (n + C * (n + 1) ^ c)
+  have hP1 : ∀ n, n + C * (n + 1) ^ c + 1 ≤ P n := by
+    intro n
+    calc n + C * (n + 1) ^ c + 1 = (n + C * (n + 1) ^ c + 1) ^ 1 := (pow_one _).symm
+      _ ≤ P n := Nat.pow_le_pow_right (by omega) (by omega)
+  have hP2 : ∀ n, (n + 1) ^ (c + 1) ≤ P n := fun n => Nat.pow_le_pow_left (by omega) _
+  obtain ⟨b, E, hE⟩ := enumCont_from_body C c G V (enumCont_bodyTM B qv qi false) (.inr 0)
+    (by
+      intro x
+      have hu := enumCont_lift_init U B hUB (fun q => .inr (.inr q))
+        (by intro q inp work; rfl) x (List.replicate (C * (x.length + 1) ^ c) true)
+        (f * (x.length + 1) ^ (c + 1)) (hU x)
+      obtain ⟨t, ht, hn, he⟩ := enumCont_body_start_guarded B hB qv qi x
+        (C * (x.length + 1) ^ c) (f * (x.length + 1) ^ (c + 1)) hu.1 hu.2
+      refine ⟨t, ht.trans ?_, hn, he⟩
+      have h1 := hP1 x.length
+      have h2 := Nat.mul_le_mul_left f (hP2 x.length)
+      have e : (3 * f + 3 * j + 60) * P x.length =
+          3 * (f * P x.length) + 3 * (j * P x.length) + 60 * P x.length := by ring
+      show _ ≤ (3 * f + 3 * j + 60) * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)
+      rw [e]
+      have : 0 ≤ j * P x.length := Nat.zero_le _
+      omega)
+    (by
+      intro x s hs
+      obtain ⟨tv, htv, hhv, hov⟩ := enumCont_verifier_call MV V Tv hV x s
+      obtain ⟨ti, hti, hhi, hoi⟩ := enumCont_increment_call I j hI x s
+      have hv := enumCont_lift_call Q B hQ hQB Sum.inl
+        (by intro q inp work; rfl) Q.tm.q₀ x s [MultiTapeTM.indicator V (x ++ s)] tv hhv hov
+      have hi := enumCont_lift_call R B hR hRB (fun q => .inr (.inl q))
+        (by intro q inp work; rfl) (.inl (some true)) x s ((incFixed s).getD []) ti hhi hoi
+      obtain ⟨t, htpos, ht, hn, he⟩ := enumCont_body_round_guarded B hB qv qi x s
+        (MultiTapeTM.indicator V (x ++ s)) tv ti hv hi
+      refine ⟨t, htpos, ?_, hn, he⟩
+      have h1 := hP1 x.length
+      have h3 : (j + 3) * (s.length + 1) ≤ (j + 3) * P x.length :=
+        Nat.mul_le_mul_left _ (by rw [hs]; omega)
+      have ht' : t ≤ 3 * (Tv (x.length + s.length) + 2 * (x.length + s.length) + 4) +
+          3 * ((j + 3) * (s.length + 1)) + 2 * x.length + 3 * s.length + 22 := by omega
+      rw [hs] at ht' h3
+      have e : (3 * f + 3 * j + 60) * P x.length =
+          3 * (f * P x.length) + 3 * ((j + 3) * P x.length) + 51 * P x.length := by ring
+      show _ ≤ (3 * f + 3 * j + 60) * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)
+      rw [e]
+      have : 0 ≤ f * P x.length := Nat.zero_le _
+      omega)
+  refine ⟨b * (A + 3), E, fun x => ?_⟩
+  obtain ⟨cfg, startup, hst, hi, hend, hout, hr⟩ := hE x
+  have hbound : b * (G x.length + (x.length + 1) ^ (c + 1) + 1) ≤
+      b * (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length) := by
+    rw [Nat.mul_assoc]
+    apply Nat.mul_le_mul_left b
+    have h1 := hP1 x.length
+    have h2 := hP2 x.length
+    show (A * P x.length + 3 * Tv (x.length + C * (x.length + 1) ^ c)) +
+      (x.length + 1) ^ (c + 1) + 1 ≤ (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length)
+    have e : (A + 3) * (Tv (x.length + C * (x.length + 1) ^ c) + P x.length) =
+        A * Tv (x.length + C * (x.length + 1) ^ c) + 3 * Tv (x.length + C * (x.length + 1) ^ c) +
+          A * P x.length + 3 * P x.length := by ring
+    rw [e]
+    have : 0 ≤ A * Tv (x.length + C * (x.length + 1) ^ c) := Nat.zero_le _
+    omega
+  refine ⟨cfg, startup, hst.trans hbound, hi, hend, hout, fun i hi' => ?_⟩
+  obtain ⟨t, ht, hh⟩ := hr i hi'
+  exact ⟨t, ht.trans hbound, hh⟩
 
 /-! **Continuation completion note (batch E2-cont A).** The historical
 partial-fill descriptions above and below are retained under the statement
@@ -2415,24 +2427,28 @@ in-place candidate replacement, and positive first-return round contracts.
 catalog-generated `2^w-1` fuel, bounded rank orbit, terminal `2^w`, and
 uniform startup/round budgets. -/
 
-/-- Assuming the single machine-construction frontier, the proved loop
-invariant gives a decider with the audited exponential-times-polynomial
-budget. This lemma inherits exactly that pending admission.
-**Proof sketch.** Start the loop after initialization, apply `enumLoop_run`
-for all `2^width` candidates, and identify its Boolean answer using exact
-candidate coverage. Since `2^width ≥ 1`, startup is absorbed by doubling the
-coefficient. The final computation has exactly one output bit. -/
-private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
-    (MV : FinTM Bool) (hV : MV.DecidesInTime V (fun n => a * (n + 1) ^ d)) :
-    ∃ (b e : ℕ) (E : FinTM Bool),
+/-- **Brute-force enumeration with an arbitrary-time verifier** [AB09, Claim 2.4, the
+enumeration argument]: if `MV` decides `V` within `Tv`, then some machine decides the
+existential projection `{x | ∃ u, |u| = C(|x|+1)^c ∧ x ++ u ∈ V}` within
+`b · 2^{C(n+1)^c} · (Tv(n + C(n+1)^c) + (n + C(n+1)^c + 1)^{c+1})`.
+
+**Proof sketch.** The loop combinator runs one round per candidate `u` of width
+`w = C(n+1)^c` (in fixed-width binary, starting from `0^w`); each round calls `MV` on
+the assembled input `x ++ u` (at most `Tv(n + w)` steps plus polynomial overhead),
+captures the verdict, restores the scratch tapes from a reversible log, and either halts
+accepting or increments `u`; after `2^w` rejecting rounds it halts rejecting. -/
+theorem exists_proj_decider (C c : ℕ) (V : Language Bool) (Tv : ℕ → ℕ)
+    (MV : FinTM Bool) (hV : MV.DecidesInTime V Tv) :
+    ∃ (b : ℕ) (E : FinTM Bool),
       E.DecidesInTime {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V}
-        (fun n => b * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ e) := by
+        (fun n => b * 2 ^ (C * (n + 1) ^ c) *
+          (Tv (n + C * (n + 1) ^ c) + (n + C * (n + 1) ^ c + 1) ^ (c + 1))) := by
   classical
-  obtain ⟨b, e, E, hE⟩ := enumMachine_contracts C c a d V MV hV
-  refine ⟨2 * b, e, E, fun x => ?_⟩
+  obtain ⟨b, E, hE⟩ := enumMachine_contracts C c V Tv MV hV
+  refine ⟨2 * b, E, fun x => ?_⟩
   obtain ⟨cfg, startup, hstartup, hinit, hend, hout, hround⟩ := hE x
   let w := C * (x.length + 1) ^ c
-  let B := b * (x.length + w + 1) ^ e
+  let B := b * (Tv (x.length + w) + (x.length + w + 1) ^ (c + 1))
   let accept := fun i => MultiTapeTM.indicator V (x ++ enumWord w i)
   obtain ⟨t, ht, hh, ho⟩ := enumLoop_run E x cfg accept B 0 (2 ^ w)
     (by simpa only [Nat.zero_add] using And.intro hend hout)
@@ -2465,54 +2481,54 @@ private theorem enumDecider (C c a d : ℕ) (V : Language Bool)
   calc startup + t ≤ B + 2 ^ w * B := Nat.add_le_add hstartup ht
        _ ≤ 2 ^ w * B + 2 ^ w * B := Nat.add_le_add_right hB _
        _ = 2 * b * 2 ^ (C * (x.length + 1) ^ c) *
-           (x.length + C * (x.length + 1) ^ c + 1) ^ e := by dsimp [B, w]; ring
+           (Tv (x.length + C * (x.length + 1) ^ c) +
+             (x.length + C * (x.length + 1) ^ c + 1) ^ (c + 1)) := by dsimp [B, w]; ring
+
 
 /-- **`NP ⊆ EXP`** [AB09, Claim 2.4]: brute-force certificate enumeration.
 
 **Proof sketch.** Let `L ∈ NP` with certificate length exactly `Q n = C(n+1)^c`
 and verifier `V ∈ P` decided by machine `MV`. The deciding machine, on input
-`x` of length `n`: evaluate the explicit formula `Q n` (a polynomial-evaluation
-machine — a **new obligation**; the explicit formula is what makes the width
-computable at all, phase-1 audit finding 1 and question 4) and lay out a
-width-`Q n` all-`false` candidate certificate; in each round, assemble
-`x ++ u` on a buffer, run `MV`, accept if it accepts, else increment the
-candidate as a **fixed-width** counter and repeat, rejecting on width overflow
-after the `2^(Q n)`-th round. Enumeration is over certificates of exactly the
-definition's length — no majorant mismatch (audit question 4). The remaining
-machine obligations, named for the fill per phase-1 finding 5 and round-2
-finding 2: fixed-width increment with overflow detection (the private
-`counterInc` layer of `ClassP/TimeConstructible.lean` extends on overflow and
-is a template, not a citable API — promotion or private re-derivation is a
-fill-time decision); retention of `x` and the candidate across rounds;
-**a verifier-call simulation that captures `MV`'s decision bit in finite
-control, suppresses its physical emissions, and redirects its halt to the
-loop controller** — the output tape is append-only, so forwarding per-round
-emissions would accumulate (`[false, true]` across two rounds) and violate
-`DecidesInTime`'s singleton contract; the real output stays empty until the
-final answer (the capture-wrapper pattern of `Turing.universalCaptureTM` is
-the in-repo precedent); reset of `MV`'s simulated state, heads, work region,
-and the captured bit between rounds (a bounded region — each head moves at
-most one cell per step); and a timed loop invariant covering all of the above
-(the untimed `exists_cond` does not supply one; at `C = 0` the single round on
-the empty certificate still executes). Budget: at most `2^(Q n)` rounds of cost polynomial in
-`n + Q n + 1`, i.e. `a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree
-`e`, small lengths absorbed into `DTIME`'s constant (the audit's own estimate):
-`L ∈ EXP`.
-+
-+**Partial-fill appendix.** The fixed-width carry, buffered captured-call
-+simulation, abstract timed-loop invariant, and final budget normalization
-+are proved below the class definitions. The machine's initialization,
-+reset, and controller assembly remain the single private admission
-+`enumMachine_contracts`; the present theorem still depends on `sorryAx`. -/
+`x` of length `n`: evaluate the explicit formula `Q n` (the explicit formula is
+what makes the width computable at all, phase-1 audit finding 1 and question 4)
+and lay out a width-`Q n` all-`false` candidate certificate; in each round,
+assemble `x ++ u` on a buffer, run `MV`, accept if it accepts, else increment
+the candidate as a **fixed-width** counter and repeat, rejecting on width
+overflow after the `2^(Q n)`-th round. Enumeration is over certificates of
+exactly the definition's length — no majorant mismatch (audit question 4). The
+verifier call is simulated with its decision bit captured in finite control, its
+physical emissions suppressed and its halt redirected to the loop controller, so
+the real output stays empty until the final answer (the output tape is
+append-only); `MV`'s simulated state, heads, work region and the captured bit are
+reset between rounds. This is the enumerator `Complexity.exists_proj_decider`
+(the fixed-width carry, buffered captured call, timed loop invariant and budget
+normalization are proved above), instantiated at `Tv = a (n+1)^d`. Budget: at
+most `2^(Q n)` rounds of cost polynomial in `n + Q n + 1`, i.e.
+`a · 2^(Q n) (n + Q n + 1)^d ≤ 2^(n^e)` for a fixed degree `e`, small lengths
+absorbed into `DTIME`'s constant: `L ∈ EXP`. -/
 theorem NP_subset_EXP : NP ⊆ EXP := by
   rintro L ⟨C, c, V, hV, hL⟩
   obtain ⟨a, d, MV, hMV⟩ := mem_P_iff.mp hV
-  obtain ⟨b, e, E, hE⟩ := enumDecider C c a d V MV hMV
-  obtain ⟨A, f, hbound⟩ := enumBudget_bound b C c e
+  obtain ⟨b, E, hE⟩ := exists_proj_decider C c V (fun n => a * (n + 1) ^ d) MV hMV
+  obtain ⟨A, f, hbound⟩ := enumBudget_bound (b * (a + 1)) C c (d + c + 1)
+  have hpoly : ∀ n : ℕ, b * 2 ^ (C * (n + 1) ^ c) *
+      (a * (n + C * (n + 1) ^ c + 1) ^ d + (n + C * (n + 1) ^ c + 1) ^ (c + 1)) ≤
+      b * (a + 1) * 2 ^ (C * (n + 1) ^ c) * (n + C * (n + 1) ^ c + 1) ^ (d + c + 1) := by
+    intro n
+    set X := n + C * (n + 1) ^ c + 1
+    have h1 : X ^ d ≤ X ^ (d + c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
+    have h2 : X ^ (c + 1) ≤ X ^ (d + c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
+    have h3 : a * X ^ d + X ^ (c + 1) ≤ (a + 1) * X ^ (d + c + 1) := by
+      have := Nat.mul_le_mul_left a h1
+      rw [Nat.add_mul, one_mul]; omega
+    calc b * 2 ^ (C * (n + 1) ^ c) * (a * X ^ d + X ^ (c + 1)) ≤
+        b * 2 ^ (C * (n + 1) ^ c) * ((a + 1) * X ^ (d + c + 1)) := Nat.mul_le_mul_left _ h3
+      _ = _ := by ring
   have heq : {x | ∃ u, u.length = C * (x.length + 1) ^ c ∧ x ++ u ∈ V} = L :=
     Set.ext (fun x => (hL x).symm)
   rw [heq] at hE
-  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x => (hE x).mono (hbound x.length)⟩
+  exact Set.mem_iUnion.mpr ⟨f, A, E, fun x =>
+    (hE x).mono ((hpoly x.length).trans (hbound x.length))⟩
 
 /-! ### A3 exponential split and clean padding verifier
 The binary evaluator below is re-derived from the pinned `e3ShiftTM`
```

## Merge #1 (`e688a482`) on `TCSlib/Complexity/ClassNP/Tautology.lean` (note 12's historical caveat)

First-parent diff; before blob `301f469537143b268ba3cc781df54039ec7d4df0`, after blob `c92b7063863ce8c1b6fe58c04f78fc432b234842`.

```diff
diff --git a/TCSlib/Complexity/ClassNP/Tautology.lean b/TCSlib/Complexity/ClassNP/Tautology.lean
index 301f4695..c92b7063 100644
--- a/TCSlib/Complexity/ClassNP/Tautology.lean
+++ b/TCSlib/Complexity/ClassNP/Tautology.lean
@@ -35,7 +35,7 @@ over the **DNF fragment**, and states Example 2.21.
   content (its hardness *is* Example 2.21's argument), while general Boolean
   formulas remain unformalized, per the audit's do-not-silently-identify
   guidance. Strings are read through the **shared** audited serialization
-  (`Std.Sat.CNF.decode`), evaluated dually. **Seeded design question (e) for
+  (`Std.Sat.DNF.decode`, delegating to `Std.Sat.CNF.decode`), as a `Std.Sat.DNF`. **Seeded design question (e) for
   the phase-4 audit.**
 * **The fallback flips sides**: the empty formula is a CNF tautology but the
   empty *disjunction* is false, so under the DNF reading non-well-formed
@@ -68,7 +68,7 @@ over the **DNF fragment**, and states Example 2.21.
 
 namespace Complexity
 
-open Std.Sat (CNF)
+open Std.Sat (CNF DNF)
 
 /-- **`coNP`-hardness** [AB09, §2.6.1]: every `coNP` language Karp-reduces to
 `L` — the mirror of the audited `Complexity.NPHard`. -/
@@ -87,31 +87,27 @@ assignment. Under the DNF reading the fallback (the empty formula, an empty
 disjunction) is *not* a tautology, so non-well-formed strings lie outside
 `TAUTOLOGY` (see the deviations list). -/
 def TAUTOLOGY : Language Bool :=
-  {x | (CNF.decode x).DNFTautology}
+  {x | (DNF.decode x).Tautology}
 
 /-! **Epoch-3 fill addition.** Private certificate and verifier machinery for
 the audited membership proof. No concurrent SAT fill is used. -/
 
-/-- Negating the literal polarities twice restores the syntax. -/
-private lemma taut_dual_dual (φ : CNF ℕ) : CNF.dual (CNF.dual φ) = φ := by
-  delta CNF.dual
-  simp [List.map_map, Function.comp_def]
-
 /-- Changing literal polarities preserves the mentioned-variable bound. -/
-private lemma taut_numVars_dual (φ : CNF ℕ) : (CNF.dual φ).numVars = φ.numVars := by
-  delta CNF.numVars CNF.dual
+private lemma taut_numVars_dual (ψ : DNF) : (DNF.dual ψ).numVars = CNF.numVars ψ.terms := by
+  delta CNF.numVars DNF.dual
   simp [List.flatMap_map, List.map_map, Function.comp_def]
 
 /-- DNF evaluation depends only on the mentioned variables.
 
 **Proof sketch.** Apply CNF evaluation congruence to the literal-negated
-formula. The proved De Morgan identity negates both values; involutivity
-and preservation of the variable bound transfer the equality back. -/
-private lemma taut_eval_congr {φ : CNF ℕ} {a b : ℕ → Bool}
-    (h : ∀ v < φ.numVars, a v = b v) : φ.evalDNF a = φ.evalDNF b := by
-  have he := eval_congr_of_lt_numVars (φ := CNF.dual φ)
+formula `DNF.dual ψ`. The proved De Morgan identity `CNF.eval_dual` negates both
+values; `DNF.dual_dual` and preservation of the variable bound transfer the
+equality back. -/
+private lemma taut_eval_congr {ψ : DNF} {a b : ℕ → Bool}
+    (h : ∀ v < CNF.numVars ψ.terms, a v = b v) : ψ.eval a = ψ.eval b := by
+  have he := eval_congr_of_lt_numVars (φ := DNF.dual ψ)
     (a := a) (b := b) (by simpa only [taut_numVars_dual] using h)
-  rw [← taut_dual_dual φ, CNF.evalDNF_dual, CNF.evalDNF_dual, he]
+  rw [← DNF.dual_dual ψ, CNF.eval_dual, CNF.eval_dual, he]
 
 /-- A finite certificate supplies false outside its explicitly stored bits. -/
 private def tautAssignment (u : List Bool) : ℕ → Bool := fun v => u.getD v false
@@ -126,19 +122,19 @@ falsifying assignment. This includes malformed strings and the empty input. -/
 private lemma taut_certificate_equiv (x : List Bool) :
     x ∈ (TAUTOLOGYᶜ : Language Bool) ↔
       ∃ u : List Bool, u.length = x.length + 1 ∧
-        (CNF.decode x).evalDNF (tautAssignment u) = false := by
+        (DNF.decode x).eval (tautAssignment u) = false := by
   classical
   have hn : x ∈ (TAUTOLOGYᶜ : Language Bool) ↔
-      ∃ a : ℕ → Bool, (CNF.decode x).evalDNF a = false := by
-    change (¬ ∀ a : ℕ → Bool, (CNF.decode x).evalDNF a = true) ↔ _
+      ∃ a : ℕ → Bool, (DNF.decode x).eval a = false := by
+    change (¬ ∀ a : ℕ → Bool, (DNF.decode x).eval a = true) ↔ _
     simp only [not_forall, Bool.not_eq_true]
   rw [hn]
   constructor
   · rintro ⟨a, ha⟩
     let u := List.ofFn (fun i : Fin (x.length + 1) => a i.val)
     refine ⟨u, List.length_ofFn, ?_⟩
-    have he : (CNF.decode x).evalDNF (tautAssignment u) =
-        (CNF.decode x).evalDNF a := by
+    have he : (DNF.decode x).eval (tautAssignment u) =
+        (DNF.decode x).eval a := by
       apply taut_eval_congr
       intro v hv
       have hv' : v < x.length + 1 := lt_of_lt_of_le hv
@@ -171,14 +167,14 @@ negates the decoded DNF only after that split has succeeded. -/
 private def tautVerifierBit (z : List Bool) : Bool :=
   match Turing.solveSplit 1 1 z.length with
   | none => false
-  | some i => !((CNF.decode (z.take i)).evalDNF (tautAssignment (z.drop i)))
+  | some i => !((DNF.decode (z.take i)).eval (tautAssignment (z.drop i)))
 
 /-- The verifier language is the accepting set of its single buffered bit. -/
 private def tautVerifier : Language Bool := {z | tautVerifierBit z = true}
 
 /-- Correctly sized certificates recover their own split and evaluation. -/
 private lemma taut_verifier_append (x u : List Bool) (hu : u.length = x.length + 1) :
-    x ++ u ∈ tautVerifier ↔ (CNF.decode x).evalDNF (tautAssignment u) = false := by
+    x ++ u ∈ tautVerifier ↔ (DNF.decode x).eval (tautAssignment u) = false := by
   have hs := taut_split_exists (x ++ u).length x.length (by simp [hu])
   change tautVerifierBit (x ++ u) = true ↔ _
   simp only [tautVerifierBit, hs, List.take_left, List.drop_left, Bool.not_eq_true']
@@ -198,8 +194,8 @@ fallback has false DNF value, so it belongs to the complement. -/
 private lemma taut_malformed (x u : List Bool) (hx : CNF.parse x = none)
     (hu : u.length = x.length + 1) :
     x ∈ (TAUTOLOGYᶜ : Language Bool) ∧ x ++ u ∈ tautVerifier := by
-  have hv : (CNF.decode x).evalDNF (tautAssignment u) = false := by
-    simp only [CNF.decode, hx, Option.getD_none]
+  have hv : (DNF.decode x).eval (tautAssignment u) = false := by
+    simp only [DNF.decode, CNF.decode, hx, Option.getD_none]
     rfl
   exact ⟨(taut_certificate_equiv x).mpr ⟨u, hu, hv⟩,
     (taut_verifier_append x u hu).mpr hv⟩
@@ -1024,7 +1020,7 @@ private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
       tautTM.tm.runFrom
         (tautCfg x (some (.evalFirst .formula)) pre.length
           (by simp [hx, universal_pair_length]) u 0) t =
-      tautCfg x none i hi u 0 [!(φ.evalDNF (tautAssignment u))] := by
+      tautCfg x none i hi u 0 [!((DNF.mk φ).eval (tautAssignment u))] := by
   induction φ with
   | nil =>
     intro x pre hx
@@ -1073,7 +1069,7 @@ private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
       · simp only [hs, List.length_cons, List.length_append]
         omega
       · rw [MultiTapeTM.runFrom_succ_eq_step', hprefix, taut_verdict]
-        delta CNF.evalDNF
+        delta DNF.eval
         simp [hv]
     | false =>
       simp only [hv, Bool.false_eq_true, ↓reduceIte] at hprefix
@@ -1082,7 +1078,7 @@ private lemma taut_formula_run (φ : CNF ℕ) (u : List Bool)
       · simp only [hs, List.length_cons, List.length_append]
         omega
       · rw [MultiTapeTM.runFrom_add, hprefix, htail]
-        delta CNF.evalDNF
+        delta DNF.eval
         simp [hv]
 
 /-- Every member of the variable-contribution list is bounded by its maximum. -/
@@ -1111,13 +1107,13 @@ with the formula run. Empty terms and the empty disjunction are covered by
 the two structural base cases; only the final verdict emits a bit. -/
 private lemma taut_machine_pair (x u : List Bool) (hu : u.length = x.length+1) :
     tautTM.ComputesInTime (pairEncode x u)
-      [!((CNF.decode x).evalDNF (tautAssignment u))] (10*((pairEncode x u).length+1)) := by
+      [!((DNF.decode x).eval (tautAssignment u))] (10*((pairEncode x u).length+1)) := by
   cases hp : CNF.parse x with
   | none =>
     have h := taut_machine_malformed x u hp
     have hm := h.mono (show 2*x.length+3 ≤ 10*((pairEncode x u).length+1) by
       rw [universal_pair_length]; omega)
-    simpa only [CNF.decode, hp, Option.getD_none] using hm
+    simpa only [DNF.decode, CNF.decode, hp, Option.getD_none] using hm
   | some φ =>
     have hx := taut_parse_shape hp
     subst x
@@ -1133,11 +1129,11 @@ private lemma taut_machine_pair (x u : List Bool) (hu : u.length = x.length+1) :
       (pairEncode (CNF.serialize φ) u) [] rfl
     simp only [List.length_nil] at heval
     have hcomp : tautTM.ComputesInTime (pairEncode (CNF.serialize φ) u)
-        [!(φ.evalDNF (tautAssignment u))] (a+b) := by
+        [!((DNF.mk φ).eval (tautAssignment u))] (a+b) := by
       apply (FinTM.computesInTime_iff _ _ _ _).mpr
       rw [MultiTapeTM.runFrom_add, hstart, heval]
       exact ⟨rfl, rfl⟩
-    rw [CNF.decode_serialize]
+    rw [DNF.decode_cnf_serialize]
     apply hcomp.mono
     rw [universal_pair_length] at ha ⊢
     omega
@@ -1237,20 +1233,20 @@ the complement.
 
 **Proof sketch.** By the definition of `Complexity.coNP`, exhibit
 `TAUTOLOGYᶜ ∈ NP`: `x ∈ TAUTOLOGYᶜ` iff some assignment falsifies the DNF
-reading of `CNF.decode x`. Certificate parameters `(1, 1)` exactly as in
+`DNF.decode x`. Certificate parameters `(1, 1)` exactly as in
 `Complexity.SAT_mem_NP` — a certificate of length `|x| + 1` carries the
 assignment on the mentioned variables (`Std.Sat.CNF.numVars_decode_le`
-bounds them by `|x|`; the evaluation-congruence bridge transfers to `evalDNF`
+bounds them by `|x|`; the evaluation-congruence bridge transfers to `DNF.eval`
 by the same mentioned-variable argument, a named obligation mirroring
 `Complexity.eval_congr_of_lt_numVars`). The verifier machine reuses the
 `SAT_mem_NP` obligations — odd-length split with explicit even rejection,
 the shared parsing machine, the assignment walk — with the **dual**
 evaluation loop: accept iff **every** term contains an unsatisfied literal,
-i.e. evaluate `evalDNF` and answer its negation (an empty term forces
+i.e. evaluate `DNF.eval` and answer its negation (an empty term forces
 rejection, the empty formula forces acceptance — round-1 audit, finding 2,
 correcting the drafted some-term phrasing) — and the buffered verdict. Malformed
 strings: the fallback is not a DNF tautology, so they lie in `TAUTOLOGYᶜ`,
-and the verifier accepts them with any certificate (`evalDNF` of `[]` is
+and the verifier accepts them with any certificate (`DNF.eval` of `⟨[]⟩` is
 `false` — consistent on both sides). -/
 theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP := by
   exact taut_membership_of_verifier taut_verifier_mem_P
@@ -1260,11 +1256,11 @@ theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP := by
 **Proof sketch.** Membership is `Complexity.TAUTOLOGY_mem_coNP`. Hardness:
 let `L ∈ coNP`, so `Lᶜ ∈ NP`, and `Complexity.SAT_NPHard` (Lemma 2.11)
 supplies `f` with `z ∈ Lᶜ ↔ f z ∈ SAT`. Set
-`g z := Std.Sat.CNF.serialize (Std.Sat.CNF.dual (CNF.decode (f z)))` — parse
+`g z := Std.Sat.DNF.serialize (Std.Sat.CNF.dual (CNF.decode (f z)))` — parse
 the Cook-Levin output, take the De Morgan dual, re-serialize. Then for every
 `z`: `z ∈ L` iff `f z ∉ SAT` iff `CNF.decode (f z)` is unsatisfiable iff its
-dual is a DNF tautology (`Std.Sat.CNF.dnfTautology_dual_iff`) iff
-`g z ∈ TAUTOLOGY` (`Std.Sat.CNF.decode_serialize` re-reads the emitted
+dual is a tautology (`Std.Sat.CNF.tautology_dual_iff`) iff
+`g z ∈ TAUTOLOGY` (`Std.Sat.DNF.decode_serialize` re-reads the emitted
 string; the decode-dual-serialize round trip is exact on every string since
 decoding is total). `Complexity.PolyTimeComputable g`: compose `f`'s machine
 (`Complexity.PolyTimeComputable.comp`) with the parse-dual-serialize
```
