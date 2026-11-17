import json, csv
rows=json.load(open('rows.json'))
S='STAGE2'
R='TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM/Reduction.lean'
ITF=("add Complexity.polyTimeComputable_iterateFind_elim (hypotheses of polyTimeComputable_iterateFind; conclusion PolyTimeComputable fun x => "
     "((List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x))).elim [] (fun i => out (g^[i] x))) in TCSlib/Complexity/Randomized/Repetition.lean; "
     "then PolyTimeComputable.congr and a case split on the local match")
ITN=("the failing read is the sealed matcher Complexity.polyTimeComputable_iterateFind.match_1 of the repetition lemma's statement (installed irreducible in the probe), "
     "unified against the local def's own match; PolyTimeComputable is not read, so the tool's polyTimeComputable_iff does not apply; same pattern as eqn item C3-0004 (Concrete.rbl_loop_poly)")
PSN="use Complexity.pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil (ClassNP/PolyTimePairing.lean, TuringMachine/Encoding.lean)"
BTZ=("add TCSlib.Cryptography.GGMRed.buildTreeQ_of_queryOf_none (queryOf l1 (next hist) = none -> buildTreeQ next b hist = .ret (verdictOf (next hist))) and "
     "GGMRed.buildTreeQ_zero_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next 0 hist = .ret false) in "+R+"; use QueryTree.simulate_ret, QueryTree.evalLazy_ret")
BTS=("add GGMRed.buildTreeQ_of_queryOf_none and GGMRed.buildTreeQ_succ_of_queryOf_some (queryOf l1 (next hist) = some x -> buildTreeQ next (b+1) hist = .query x (fun o => buildTreeQ next b (hist ++ [(x, o)]))) in "
     +R+"; use QueryTree.simulate_query, QueryTree.evalLazy_query, simulate_ret, evalLazy_ret")
BTN=("after rw [buildTreeQ_zero/succ] the `cases ... <;> rfl` must iota-reduce the sealed matcher GGMRed.buildTreeQ.match_1 on none/some and unfold QueryTree.simulate/evalLazy; "
     "verdictOf occurs identically on both sides and is not read; the existing buildTreeQ_zero/succ readers keep the match, so case readers are needed")
STA=("add TCSlib.Cryptography.GGMRed.start_eq (start X = pairEncode [] (pairEncode [] (pairEncode [] []))) and GGMRed.tblOf_nil (tblOf val [] k = []) in "+R+"; use GGMRed.histEnc_eq, GGMRed.tblEnc_nil")
GGD=("add TCSlib.Cryptography.ggmBitsDist_apply (ggmBitsDist G A q i j z c = ggmDist (splitHalves o G) A q i j (splitHalves z) c), ggmDist_eq (ggmDist G A q i j = tableDist G (levelAdv G i A) q j) "
     "and levelAdv_apply (levelAdv G i A r = (A r).simulate (fun x => prefixAt x i) (fun x v => ggmFrom G x (i + 1) (pairSel (x i) v))) in TCSlib/Cryptography/Pseudorandom/Functions/GGM.lean; "
     "add tableDist_apply (tableDist G A q j z c = (A c.2).evalLazy (challengeStream G j z c.1) []) in TCSlib/Cryptography/Pseudorandom/Functions/SubHybrids.lean; use challengeStream_def")
QOF=("add TCSlib.Cryptography.GGMRed.queryOf_eq_some_iff_decode (queryOf l w = some x <-> exists y, pairDecode w = some ([false], y) and decodeFin l y = some x) in "+R+
     " (or move queryOf_eq_some_iff itself next to queryOf); the `split at h` on the foreign matcher queryOf.match_1 (via queryOf_eq) is then not needed")
QON=("generated-equation read of the foreign matcher GGMRed.queryOf.match_1 (splitter/eq_2) by `split at h` after simp only [queryOf_eq]; a reader named after the matcher (queryOf.match_1_eq) is not a natural Stage 2 reader")
SMP=("add TCSlib.Cryptography.Ensemble.samplable_iff (X.Samplable <-> exists s S, PolyTimeComputable S and forall n, StatClose (fun r : Fin (s.eval n) -> Bool => padFin (l.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0) in TCSlib/Cryptography/Asymptotic/Ensembles.lean")
OWPAIR="add TCSlib.Cryptography.owpPair_apply (owpPair f w = (f w.1, w.2)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean; use owpPredictor_apply"
OWGEN="add TCSlib.Cryptography.owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean"
LAC="use Complexity.NUPPT.layout_eq, Complexity.NUPPT.advInput_eq and Complexity.NUPPT.coinLen_eq (Randomized/Closure.lean, Randomized/PPT.lean)"
LACN=("goal: Enc.output (layout (replicate n true) y [] (coinBlock (Enc.coins.eval n) i r)) = Enc.output (pairEncode (pairEncode (advInput n y) []) (coinBlock (Enc.coinLen n) i r)); "
      "reads layout, advInput and coinLen (coinBlock occurs on both sides and is not read)")
DAD="use TCSlib.Cryptography.distAdv_def (TCSlib/Cryptography/Foundations/Experiments.lean)"
EXPG=("use TCSlib.Cryptography.prgExt_def (TCSlib/Cryptography/Pseudorandom/Generators.lean); add TCSlib.Cryptography.prgStep_eq (prgStep G s = (G s).2) in TCSlib/Cryptography/Pseudorandom/Generators.lean; with the local oneBitStep_eq")
UNK="proof-only fix to be identified in the infoview (set_option pp.explicit true): the residual goal prints as X = X, so the sides differ only in hidden arguments"
D={}
def put(ids,cls,st,fix,note):
    for i in ids.split(): D[i]=(cls,st,fix,note)
put('SEAL-0207 EFF72:SEAL-0207',S,'no',ITF,'CHANGED fix. stateLoopFun_poly l.299 `exact hF.comp hpre`: '+ITN)
put('SEAL-0209',S,'no',ITF,'CHANGED fix. lookup_poly l.422 (term proof): '+ITN)
put('H:52 SEAL-0208',S,'no',PSN,'CHANGED fix (refined). l.400 `have h3 : pairSndD ([] : List Bool) = [] := rfl` reads pairSndD; pairSndD_eq alone still needs pairDecode_nil')
put('H:53 SEAL-0210',S,'no',PSN+'; with GGMRed.tblEnc_nil','CHANGED fix. l.439 rfl on pairEncode p (pairSndD (tblEnc [])) = pairEncode p (tblEnc []): the read is pairSndD (after pairFstD_pairEncode/pairSndD_pairEncode), not pairFstD')
put('H:55 SEAL-0211 SEAL-0212',S,'no',BTZ,'CHANGED fix. concrete_zero l.101 (SEAL-0211 none case, SEAL-0212 some case): '+BTN)
put('H:56 SEAL-0213 SEAL-0214',S,'no',BTS,'CHANGED fix. concrete_succ l.112/113 (SEAL-0213 none, SEAL-0214 some): '+BTN)
put('H:57 SEAL-0215',S,'no',STA,'CHANGED class STATEMENT->STAGE2, statement_level yes->no. start_rawInput is a one-line declaration (l.272): the error is the proof term `rfl` (Type mismatch rfl), the header elaborates (it only mentions start); after start_eq the rfl still needs histEnc [] and tblOf val [] 0, hence the extra readers')
put('H:58 SEAL-0216',S,'no','use Complexity.NUPPT.runAt_eq and Complexity.NUPPT.runAtL_eq_output_layout (Randomized/PPT.lean, Randomized/Closure.lean) after unfolding the local nextQ','CHANGED fix. move_eq l.362 rfl: D.output (layout (replicate n true) (histEnc s.1) (advice n) (ofFn d.r)) = nextQ d s.1 = D.runAt n (histEnc s.1) d.r; layout_eq alone leaves runAt/advInput; histEnc is not read')
put('H:59 SEAL-0217',S,'no','use Complexity.StateLoop.orbit_zero (TCSlib/Complexity/Randomized/Build/StateLoop.lean)','CHANGED fix. The failing step is the `| 0, _ => start_rawInput d` branch (l.524): orbit start step x 0 = start x; orbit_succ is already used in the succ branch. Also depends on start_rawInput (SEAL-0215)')
put('H:60 SEAL-0218',S,'no','use Complexity.NUPPT.layout_eq and Complexity.NUPPT.advInput_eq (Randomized/Closure.lean, Randomized/PPT.lean)','CHANGED fix (completed). l.736 rfl: rawFun (pairEncode (pairEncode (advInput n y) a) c) = rawFun (layout (replicate n true) y a c); both readers are needed')
put('H:61 SEAL-0219',S,'no',GGD,'CHANGED fix. l.769 `hrhs : ggmBitsDist G (...) ... = concrete ... := rfl` unfolds ggmBitsDist/ggmDist/levelAdv/tableDist (no readers in readers-v4) down to evalLazy of the simulated buildTreeQ; coinLen is not read')
put('C3-0002 C3-0003 NEW:294',S,'no',QOF,'CHANGED fix. '+QON+'. C3-0002 (record: eq_2, old module prefix GGMReductionEval) and NEW:294 (eq_2, current prefix) look like the same reference; C3-0002 evidence points at eqrefs.tsv:2 (splitter): lead to dedupe')
put('SEAL-0260',S,'no','use TCSlib.Cryptography.Ensemble.pseudorandom_iff and TCSlib.Cryptography.prgAdv_eq; add Ensemble.indist_iff (X.Indist Y <-> forall D, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (l.eval n))) and Ensemble.distAdv_uniform (distAdv X ((uniform l).X n) D = distAdv X id D) in TCSlib/Cryptography/Asymptotic/Ensembles.lean',
    'CHANGED fix. l.94 Iff.rfl reads Ensemble.Pseudorandom, Ensemble.Indist (no definitional reader: only indist_iff_exists_negligible), uniform.X and prgAdv; Negligible occurs on both sides and is not read (negligible_iff does not help)')
put('SEAL-0261',S,'no','use TCSlib.Cryptography.Ensemble.pseudorandom_iff (TCSlib/Cryptography/Asymptotic/Ensembles.lean)','confirmed (l.99 Indist.refl against (uniform l).Pseudorandom)')
put('SEAL-0262',S,'no','use TCSlib.Cryptography.Ensemble.pseudorandom_iff (TCSlib/Cryptography/Asymptotic/Ensembles.lean) on hY and on the goal','CHANGED fix (was: reader to be identified). l.105 h.trans hY: hY : Y.Pseudorandom expected Y.Indist _; the read is Ensemble.Pseudorandom')
put('SEAL-0263',S,'no','use TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv (this file, repaired per SEAL-0260) with the local PRG.ensemble_X; PRG.Secure is local',
    'CHANGED fix. l.189 Iff.rfl: P.Secure is local, the foreign reads are those of pseudorandom_iff_prgAdv (Pseudorandom/Indist/prgAdv); negligible_iff does not apply')
put('SEAL-0264 SEAL-0265',S,'no',SMP,'CHANGED fix. l.198 refine with anonymous constructor: the expected type P.ensemble.Samplable is the sealed def Ensemble.Samplable (no definitional reader in readers-v4: only uniform_samplable); SEAL-0265 (l.199 No goals) is its cascade. The NUPPT.advInput read at l.203 is the separate scan item C1-0277')
put('C1-0277',S,'no','use Complexity.NUPPT.advInput_eq (TCSlib/Complexity/Randomized/PPT.lean)','confirmed (scan: simp [NUPPT.advInput, ...] at l.203)')
put('H:64 SEAL-0223',S,'no',EXPG,'CHANGED class STATEMENT->STAGE2, statement_level yes->no. expand_G: the error at l.116 is the proof term `rfl` on the last header line; the statement reads only the local PRG.expand and elaborates; the rfl unfolds prgExt and prgStep (no prgStep reader in readers-v4)')
put('H:65 SEAL-0224',S,'no','use TCSlib.Cryptography.acceptProb_def (TCSlib/Cryptography/Foundations/Experiments.lean)','confirmed (l.152 rfl between acceptProb terms after acceptProb_fst)')
put('H:66',S,'no','l.217: use the local PRG.expand_G (after SEAL-0223); l.230: add TCSlib.Cryptography.expandRedMachine_coinsEquiv in Pseudorandom/Generators/Asymptotic/StretchMachine.lean; l.241: use prgAdv_eq and distAdv_def','CHANGED fix. Three independent reads, see SEAL-0225..0227; polyTimeComputable_iff does not apply to any of them')
put('SEAL-0225',S,'no','use TCSlib.Cryptography.PRG.expand_G (this file; repaired per SEAL-0223)','CHANGED fix. l.217 `rfl` in the Easy branch: List.ofFn (closed form) = List.ofFn ((PRG.expand G l hl).G n s) unfolds PRG.expand -> prgExt/prgStep; PolyTimeComputable is not read')
put('SEAL-0226',S,'no','add TCSlib.Cryptography.expandRedMachine_coinsEquiv ((expandRedMachine D hF l k hk).Coins n ~= (Fin (l.eval n) -> Bool) x D.Coins n, with List.ofFn (e.symm (a, c)) = List.ofFn a ++ List.ofFn c) in TCSlib/Cryptography/Pseudorandom/Generators/Asymptotic/StretchMachine.lean (built from Complexity.NUPPT.wrapCoinsEquiv and Fin.appendEquiv)',
    'CHANGED fix. l.230: Fin.appendEquiv (l.eval n) (D.coinLen n) is used at type ... ~= (expandRedMachine ...).Coins n, which needs the coins field of expandRedMachine (= D.wrap ..., coins_wrap) and coinLen; flagged cascade by the tool but independent of l.217')
put('SEAL-0227',S,'no','use TCSlib.Cryptography.prgAdv_eq (Pseudorandom/Generators.lean) and TCSlib.Cryptography.distAdv_def (Foundations/Experiments.lean)','CHANGED fix. l.241 abs_nonneg _ against 0 <= prgAdv ...: reads prgAdv and distAdv; h3 at l.243 has the same pattern')
put('H:63',S,'no',OWPAIR.replace('; use owpPredictor_apply','')+'; also add owpGen_apply (owpGen f B w = (f w.1, w.2, B w)) there; use owpPredictor_apply and the local owpPredictorSnoc_eq','CHANGED fix (completed): l.153 reads owpPair (SEAL-0221), l.159 reads owpGen (SEAL-0222)')
put('SEAL-0221',S,'no',OWPAIR+' and the local owpPredictorSnoc_eq','confirmed (reader named owpPair_apply). l.153 fun _ => Iff.rfl: owpPair f (s, ()) must reduce to (f s, ()); the let-bound e unfolds locally')
put('SEAL-0222',S,'no',OWGEN,'CHANGED fix. l.159 rfl: acceptProb (fun z => Fin.snoc (f z.1) (B z.1)) D vs acceptProb (fun s => e (owpGen f _ s)) D: the read is owpGen, not owpPair')
put('H:107 SEAL-0266 SEAL-0267',S,'no',DAD,'confirmed (l.182 abs_nonneg and l.190 abs_sub_comm against distAdv)')
put('H:108 SEAL-0268',S,'no','use TCSlib.Cryptography.blockState_eq (TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean)','CHANGED fix. l.203: the expected PolyTimeComputable fun z => blockState (inParam z) ... vs the nested pairEncode: the read is blockState; inArg occurs on both sides and is not read')
put('H:109 SEAL-0269',S,'no',LAC,'CHANGED fix (completed). bitwise_enc_runAtL l.247: '+LACN)
put('H:110',S,'no','use TCSlib.Cryptography.distAdv_def (l.479) and TCSlib.Cryptography.singleDist_def, TCSlib.Cryptography.multiDist_eq (Encryption/PublicKey/Hybrid.lean) (l.455)','CHANGED fix (completed), see SEAL-0270/0271')
put('SEAL-0270',S,'no',DAD,'confirmed (l.479 hε0: abs_nonneg against distAdv)')
put('SEAL-0271',S,'no','use TCSlib.Cryptography.singleDist_def and TCSlib.Cryptography.multiDist_eq (TCSlib/Cryptography/Encryption/PublicKey/Hybrid.lean)','CHANGED fix. l.455 unsolved goal: the final `exact hB n ...` must identify multiDist/singleDist (Hybrid.lean) with the local pkMultiEncDist/pkEncDist; distAdv is not the read')
put('H:111 SEAL-0272',S,'no',OWPAIR,'confirmed (reader named owpPair_apply). predProb_pkPredictor_eq l.292 Iff.rfl reads owpPair and owpPredictor (owpPredictor_apply published)')
put('H:112 SEAL-0273',S,'no',OWGEN,'confirmed (reader named owpGen_apply). acceptProb_owpGen_unit l.300')
put('H:113 SEAL-0274',S,'no','add TCSlib.Cryptography.owpGenNot_apply (owpGenNot f B w = (f w.1, w.2, !B w)) in TCSlib/Cryptography/Pseudorandom/GeneratorFromPermutation.lean','CHANGED fix. l.308: simp only [acceptProb_def] has already run (the goal shows the unfolded uprob predicate); the remaining read is owpGenNot (no reader)')
put('H:114 SEAL-0275',S,'no',LAC,'CHANGED fix. blockEncFun_flatten l.181 rfl after hEnc.runAtL_eq: '+LACN+'; uniform_iff does not apply')
put('H:115 SEAL-0276',S,'no','use TCSlib.Cryptography.distAdv_comp (TCSlib/Cryptography/Pseudorandom/Indistinguishability.lean) with P := fun w => pairEncode w.1 (encodeList (List.ofFn w.2))','CHANGED fix. l.246 calc step `:= rfl` equates distAdv of encoded samples with distAdv against the encoding distinguisher: exactly distAdv_comp; encodeList/pairEncode occur on both sides and are not read')
put('H:116',S,'no','l.322: '+UNK+'; l.330: use TCSlib.Cryptography.distAdv_def on hsingle','CHANGED fix, see SEAL-0277/0278')
put('SEAL-0277',S,'no',UNK+' (likely a stale Decidable instance or an implicit coin length, Enc.coinLen n vs Enc.coins.eval n)','CHANGED fix; UNRESOLVED. l.322 simp only [singleDist, hybridAdv, distinguisherL_eq, runAt_eq, ofFn_hybridCoins, hB ...] leaves decide (...) = decide (...) with identical printed sides; tool pick pairFstD_eq is not supported by the goal')
put('SEAL-0278',S,'no','use TCSlib.Cryptography.distAdv_def on hsingle (simpa only [distAdv_def] using hsingle _ _)','CHANGED fix. l.330 exact hsingle _ _: hsingle is stated with distAdv, the goal was rewritten to |acceptProb - acceptProb| by distAdv_def')
put('H:117 SEAL-0279',S,'no',UNK+'; candidate: close with decide_eq_decide / Bool.decide_congr',
    'CHANGED class STATEMENT->STAGE2, statement_level yes->no; UNRESOLVED fix. tdpPredictor_runAtL: "unsolved goals" is reported at the `by` that ends the header line 114; the goal is left by the closing simp of the proof (decide P = decide P, printed sides identical), not by the statement')
put('H:118 SEAL-0280',S,'no','proof-only: rewrite the right-hand ite with the local ite_eq_xor_not before unfolding NUPPT.distinguisherL (or state ite_eq_xor_not for an arbitrary Decidable instance); readers NUPPT.distinguisherL_eq and NUPPT.runAt_eq are already used',
    'CHANGED class STATEMENT->STAGE2, statement_level yes->no; fix low-confidence. uprob_tdpPredictor: "unsolved goals" (case e_p.h) is reported at the `by` on header line 157 and is the residual of the final simp only (ite_eq_xor_not did not fire on if decide (...) = true then c else !c), so the failure is in the proof')
D['NEW:139']=None  # strict confirm
for i in ('NEW:150','NEW:151'): D[i]='HARNESS'
out=[]; changed=[]
for r in rows:
    i=r['item_id']
    tool=(r['class'],r['statement_level'],r['fix'])
    if r['class'] in ('SEAL-B-ONLY','STRICT-ONLY (notation, no fix)') and i not in D or D.get(i,1) is None:
        dec=(tool[0],tool[1],tool[2],'confirmed (counts strict_A=%s strict_B=%s coe_A=%s coe_B=%s fit the class)'%(r['strict_A'],r['strict_B'],r['coe_A'],r['coe_B']))
    elif D.get(i)=='HARNESS':
        dec=(tool[0],tool[1],tool[2],'HARNESS: inherited_source_attribute_interaction (lead decides). l.68 is the file\'s own attribute [local irreducible] uprob acceptProb meeting the seal\'s attribute (failed to set [local irreducible], X is currently [irreducible]); not Stage 2 debt')
    else:
        dec=D[i]
    for f in dec: assert '\t' not in f and '\n' not in f
    out.append((r['key'],)+dec)
    if dec[0]!=tool[0] or dec[1]!=tool[1]: changed.append((i,tool[0],dec[0],tool[1],dec[1]))
assert len(out)==120 and len(set(o[0] for o in out))==120
O='/home/user/dw10/exch/inbox/audits/dw10-seal-inventory/evidence/subagents/sub-B/overrides-sub-B.tsv'
with open(O,'w') as f:
    f.write('key\tclass\tstatement_level\tfix\tnote\n')
    for o in out: f.write('\t'.join(o)+'\n')
fixchg=sum(1 for r,o in zip(rows,out) if o[3]!=r['fix'])
print('rows',len(out),'class/stmt changed',len(changed),'fix text changed',fixchg)
for c in changed: print(c)
from collections import Counter
print(Counter(o[1] for o in out))
