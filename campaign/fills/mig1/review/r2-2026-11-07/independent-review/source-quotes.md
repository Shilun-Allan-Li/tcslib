## REPORT.md:20

```text
20:    through published equations.
21: 2. `0b88b8e3` — the T3-factored bank lemmas use the published `Turing.embedEmitCfg_unselected`
22:    instead of the time-0 instance of `embedEmitTM_frame` (a definitional `runFrom 0` read);
23:    CodeSimulator reads two more seam states through `Cfg.ofWords_state`.
24: 3. `246d81d2` — `pairMapSndTM_computes` (a new public proof) and the moved `fwdMap_finish` no longer
25:    pass Encoding's `pairEncode` (nor `initCfg`/`Cfg.init`) to `simp`; they use the published
26:    `Turing.pairEncode_eq`.
27: 
```

## REPORT.md:58

```text
58:   (`Seal_PrimitivesR3.*`, now also sealing `Turing.pairEncode`): **17 errors, all in
59:   verbatim-moved material** (`fwdMap_*`, `poly_space`); the new public proofs and the three specs
60:   have no foreign definition among their `simp`/`rw`/`unfold` arguments (`argscan/Primitives.txt`).
61:   **CertShell/CodeSimulator strict runs** (also sealing `Cfg.ofWords`): the reads introduced by
62:   this fill are fixed; what remains are pre-existing reads elsewhere in the same declarations —
63:   `(vhostCfg …).state` in `cert_prepare_exists` and `Cfg.mapState` of a `Cfg.ofWords` seam in
64:   `canonPreserveInstall` (E3).
65: 
66: ## Updated dispositions and escalations
67: - MIG-24: **T1 done** (Simulation, Loop, Primitives); **T3 partial**; T2, T5 not done; T2b as
68:   revision 1 (replay pair not factored); T4, T6 done; T7 inspected.
69: - **E3** (new; pre-existing reads, no published statement): `Turing.Cfg.ofWords_mapState :
70:   (Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w` (Convention) and
71:   `Turing.vhostCfg_state : (vhostCfg c tag p pre).state = c.state.map …` (VirtualInput), or
72:   `simps` field equations for `vhostCfg`.
73: - E1, E2 unchanged.
```

## source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt:2723

```text
2723: private lemma fwdMap_move (M : FinTM Bool) (x : List Bool)
2724:     (q q' : Option (FwdMapState M.State)) (p : Fin (x.length + 2))
2725:     (a b : List Bool) (ha hb : ℤ) (out : List Bool)
2726:     (mi ma mb : SignType) (emit : Option Bool) :
2727:     (fwdMapAct M mi (none, ma) (none, mb) emit q').apply
2728:       (fwdMapCfg M x q p a b ha hb out) =
2729:       fwdMapCfg M x q' (moveInputPos p mi) a b (ha + ma.cast) (hb + mb.cast)
2730:         (out ++ emit.toList) := by
2731:   refine Cfg.ext (Action.apply_state _ _) (Action.apply_inputPos _ _) ?_ ?_
2732:     (Action.apply_output _ _)
2733:   · funext i
2734:     refine Fin.addCases (fun j => ?_) (fun j => ?_) i
2735:     · simp [fwdMapAct, fwdMapCfg, Action.apply]
2736:     · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
2737:         simp [fwdMapAct, fwdMapCfg, Action.apply]
2738:   · funext i
2739:     refine Fin.addCases (fun j => ?_) (fun j => ?_) i
2740:     · simp [fwdMapAct, fwdMapCfg, Action.apply]
2741:     · refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
2742:         simp [fwdMapAct, fwdMapCfg, Action.apply]
2743: 
```

## source/TCSlib/Complexity/TuringMachine/Build/Primitives.lean.txt:2990

```text
2990: private lemma fwdMap_finish (M : FinTM Bool) (x pre a b : List Bool)
2991:     (hx : x = pre ++ b) :
2992:     (fwdMapTM M false).tm.runFrom
2993:       (fwdMapCfg M x (some .copyB) ⟨pre.length + 1, by simp [hx] <;> omega⟩
2994:         a [] (a.length - 1) 0 []) (3 * a.length + 2 * b.length + 5) =
2995:       fwdMapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a (pairEncode a []) := by
2996:   rw [show 3 * a.length + 2 * b.length + 5 =
2997:       ((b.length + 1) + (b.length + 1) + (a.length + 1)) + (2 * a.length + 2) by omega,
2998:     MultiTapeTM.runFrom_add (a := (b.length + 1) + (b.length + 1) + (a.length + 1)) (b := 2 * a.length + 2),
2999:     MultiTapeTM.runFrom_add (a := (b.length + 1) + (b.length + 1)) (b := a.length + 1),
3000:     MultiTapeTM.runFrom_add (a := b.length + 1) (b := b.length + 1)]
3001:   have hcopy := fwdMap_suffix M x b a pre [] hx
3002:   simp only [List.nil_append, List.length_nil, Nat.cast_zero] at hcopy
3003:   rw [hcopy]
3004:   rw [fwdMap_backB M x a b _ _ (le_refl _), fwdMap_backA M x a b _ _ (le_refl _)]
3005:   have he := fwdMap_emit M x a b a (⟨x.length + 1, by omega⟩) [] [] (by simp)
3006:   simp only [List.length_nil, Nat.cast_zero, List.nil_append] at he
3007:   rw [he]
3008:   refine Cfg.ext rfl rfl rfl ?_ ?_
3009:   · funext i
3010:     simp [fwdMapCfg, fwdMapVirtual, MultiTapeTM.initCfg, Cfg.init]
3011:   · simp [fwdMapCfg, fwdMapVirtual, pairEncode_eq]
3012: 
```

## source/TCSlib/Complexity/TuringMachine/Build/Loop.lean.txt:4454

```text
4454: private lemma emCall_bank_initial (M : FinTM Bool) (emit : Bool)
4455:     (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
4456:     let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
4457:     emCallEmbeddedCfg (emCallTripleEmbedding M i) (fun q => .inr (.inl (i.castSucc, q)))
4458:       frame.workTapes frame.workTapePos
4459:       (emCallClearCfg x 1 0 ((M.tm.runFrom (M.tm.initCfg arg) T).workTapes i)
4460:         (emCallSpan (emCallLo M arg T i) (emCallHi M arg T i)) (bufferTape [true])
4461:         ((M.tm.runFrom (M.tm.initCfg arg) T).workTapePos i)) = frame := by
4462:   dsimp only
4463:   refine Cfg.ext rfl rfl ?_ ?_ rfl
4464:   · funext j
4465:     simp only [emCallEmbeddedCfg, Cfg.mapState]
4466:     rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
4467:     · subst j
```

## source/TCSlib/Complexity/TuringMachine/Build/Loop.lean.txt:4518

```text
4518: private lemma emCall_bank_final (M : FinTM Bool) (emit : Bool)
4519:     (x arg cap : List Bool) (T : ℕ) (i : Fin M.k) :
4520:     let frame := emCallBankFrame M emit x arg cap T i.val (.inr (.inl (i.castSucc, 0)))
4521:     emCallEmbeddedCfg (emCallTripleEmbedding M i) (fun q => .inr (.inl (i.castSucc, q)))
4522:       frame.workTapes frame.workTapePos
4523:       (emCallClearCfg x 1 3 (fun _ => none) (fun _ => none) (fun _ => none) 0) =
4524:       emCallBankFrame M emit x arg cap T (i.val + 1) (.inr (.inl (i.castSucc, 3))) := by
4525:   dsimp only
4526:   refine Cfg.ext rfl rfl ?_ ?_ rfl
4527:   · funext j
4528:     simp only [emCallEmbeddedCfg, Cfg.mapState]
4529:     rcases emCall_layout_cases M j with h | h | ⟨l, r, h⟩
4530:     · subst j
```

## source/TCSlib/Complexity/TuringMachine/CodeSimulator.lean.txt:1303

```text
1303:       ((Cfg.ofWords (input := x) SweepPhase.done copied).mapState fun _ => enter) t₁ =
1304:       Cfg.ofWords leave result := second
1305:   have cut' (u : ℕ) (hu : u < t₁) :
1306:       (E.runFrom ((Cfg.ofWords (input := x) SweepPhase.done copied).mapState
1307:         fun _ => enter) u).state ≠ some leave := secondCut u hu
1308:   have whole := seamCompTM_run_ofCfg P .done E enter run₀ (Cfg.ofWords_state _ _) cut₀ second'
1309:   have first := seamCompTM_firstReturn_ofCfg P .done E enter leave
1310:     run₀ (Cfg.ofWords_state _ _) cut₀ second' rfl cut'
1311:   refine ⟨t₀ + 1 + t₁, ?_, ?_, ?_⟩
1312:   · calc
1313:       t₀ + 1 + t₁ ≤ 3 * arg.length + 4 +
1314:           a * (T arg.length + arg.length + (f arg).length + 1) := by omega
1315:       _ ≤ (a + 4) * (T arg.length + arg.length + (f arg).length + 1) := by
1316:         rw [Nat.add_mul]
1317:         omega
1318:   · simpa only [C, Cfg.ofWords, Cfg.mapState, Option.map_some] using first
1319:   · simpa only [C, result, w, Cfg.ofWords, Cfg.mapState, Option.map_some] using whole
1320: 
1321: 
```

## Existing VirtualInput.lean:135

SHA-256 `8cf6b4469661b82a828a721e7504794b4240bbb338817a95fac8ca43eacee2aa`

```text
135: def vhostCfg (c : Cfg m Bool S y) (b : Bool) (p : Fin (x.length + 2))
136:     (pre : List Bool) : Cfg (1 + m) Bool (S × Bool) x where
137:   state := c.state.map (fun q => (q, b))
138:   inputPos := p
139:   workTapes := Fin.addCases (fun _ => FinTM.bufferTape y) c.workTapes
140:   workTapePos := Fin.addCases (fun _ => (c.inputPos.val : ℤ) - 1) c.workTapePos
141:   output := pre ++ c.output
142: 
143: /-! Z1's configuration fields as equations (the ND inventory API, 2026-10-17), by `simps` without
144: the `simp` attribute: the state is `c`'s tagged by `b`, the input head is `p`, tape `0` is the
145: buffer of `y` with its head at `c.inputPos - 1`, the other tapes and heads are `c`'s, and the output
146: is `pre ++ c.output`. -/
147: attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]
148:   vhostCfg
```
