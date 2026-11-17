# lead_overrides.py (dw10-seal-inventory, Claude lead, 2026-11-17): NEW. Usage: python3 -I lead_overrides.py <out overrides-lead.tsv>
# Lead classification review (dw10-seal-inventory): builds overrides-lead.tsv for the lead's open items.
# Rules by (file, declaration) for seal items (first coe-A error inspected by the lead) and by (file, provider) for scan items.
import csv, json, re, sys
E='/home/user/dw10/exch/inbox/audits/dw10-seal-inventory/evidence'
rows=[r for r in csv.DictReader(open(E+'/review/open-items.tsv'),delimiter='\t') if r['agent']=='lead']
APPLY=("use the field equations of Turing.Action.apply for the fields compared: Turing.Action.apply_state, apply_output, "
       "apply_inputPos, apply_workTapePos (Configuration.lean), apply_workTapes (Simulation.lean)")
STEPOF=("use Turing.MultiTapeTM.step_of_some (Deterministic.lean, with the state hypothesis; step_of_halt when halted) in place "
        "of unfolding MultiTapeTM.step, then the Action.apply field equations")
RUNCH=("use Turing.MultiTapeTM.runFrom_succ_eq_step and runFrom_zero to rewrite the runFrom goal to two steps (the `change` "
       "reads runFrom), then Turing.MultiTapeTM.step_of_some")
INIT=("use Turing.MultiTapeTM.initCfg_eq and the field equations of Turing.Cfg.init (init_state, init_output, init_inputPos, "
      "init_workTapes, init_workTapePos; Configuration.lean)")
PD=("provider TCSlib/Complexity/TuringMachine/Encoding.lean: add the case equations of Turing.pairDecode "
    "(pairDecode (false :: false :: r) = (pairDecode r).map (fun p => (false :: p.1, p.2)); the same for true :: true; "
    "pairDecode (false :: true :: r) = some ([], r); pairDecode [b] = none; pairDecode (true :: false :: r) = none); "
    "only pairDecode_nil is published and the step computes other branches")
D = {  # (file suffix, declaration last component) -> (class, fix, note)
 ('OneWayYao.lean','statClose_sampleAll'):('STAGE2','add TCSlib.Cryptography.OneWay.YaoMachine.sampleAll_eq (sampleAll T n hM as the equivalence-pushed product of the round samplers; proved by unfold) next to sampleAll in OneWayYao.lean; coinLen_eq does not reach the read','changed reader (was STATEMENT by the line-only test); needs a check'),
 ('OneWayYao.lean','yaoRaw_poly'):('STAGE2','add TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw_eq (yaoRaw D T = fun x => match the iterateFind search; proved by unfold) next to yaoRaw and rewrite with it before polyTimeComputable_iterateFind','changed reader: the read is yaoRaw, not PolyTimeComputable'),
 ('UniversalPadding.lean','lengthRegular_gStr'):('STAGE2','add TCSlib.Cryptography.FunFamily.lengthRegular_iff (the unfolded LengthRegular condition) in TCSlib/Cryptography/Asymptotic/OneWay.lean (an owner)','was STATEMENT by the line-only test; the error is the proof term after `:=`'),
 ('UniversalPadding.lean','family_inLen'):('STAGE2','prove the reader without rfl through the definition: `unfold family` / family.eq_def (family is sealed after its definition in the whole-file seal)','was STATEMENT by the line-only test; the reader itself reads its own-file definition'),
 ('EnsemblesLemmas.lean','acceptProb_reparam'):('STAGE2','use Complexity.NUPPT.distinguisher_eq and distinguisherL_eq (Adversary.lean) with hB to close the pointwise distinguisher goal','was STATEMENT by the line-only test; needs a check'),
 ('EnsemblesLemmas.lean','acceptProb_reparam_advice'):('STAGE2','use Complexity.NUPPT.distinguisher_eq and distinguisherL_eq (Adversary.lean) with hA to close the pointwise distinguisher goal','was STATEMENT by the line-only test; needs a check'),
 ('EnsemblesLemmas.lean','acceptProb_pushRed'):('STAGE2','use Complexity.NUPPT.distinguisher_eq and distinguisherL_eq (Adversary.lean) with hB; padFin is not the read','was STATEMENT by the line-only test; needs a check'),
 ('UniversalLemmas.lean','length_signBits'):('STAGE2','use Turing.signBits_neg, signBits_zero and signBits_pos (Encoding.lean; one per case)','was STATEMENT by the line-only test; all three case lemmas'),
 ('Ensembles.lean','indist_iff_exists_negligible'):('STAGE2','use TCSlib.Cryptography.distAdv_def','confirmed'),
 ('Ensembles.lean','symm'):('STAGE2','use TCSlib.Cryptography.distAdv_def','confirmed'),
 ('Ensembles.lean','trans'):('STAGE2','use TCSlib.Cryptography.distAdv_def','confirmed'),
 ('Ensembles.lean','toIndist'):('STAGE2','use Complexity.NUPPT.coinLen_eq (rewrite D.coinLen to D.coins.eval before eval_mono)','resolved: the step compares coinLen with coins.eval'),
 ('Ensembles.lean','hybrid_lemma'):('STAGE2','use TCSlib.Cryptography.distAdv_def','changed reader: the expected type reads distAdv (acceptProb is its body)'),
 ('Ensembles.lean','copies'):('STAGE2','use TCSlib.Cryptography.acceptProb_def (rewrite both sides before OneWay.uprob_congr)','changed reader: the stuck Fintype is the sample space of the sealed acceptProb, not advInput'),
 ('Ensembles.lean','predict_eq'):('STAGE2','use TCSlib.Cryptography.acceptProb_def','confirmed'),
 ('Ensembles.lean','prediction_lemma'):('STAGE2','use TCSlib.Cryptography.distAdv_def','changed reader: abs_sub_comm needs distAdv as an absolute value'),
 ('EnsemblesLemmas.lean','acceptProb_coins_equiv'):('STAGE2','use TCSlib.Cryptography.acceptProb_def','confirmed'),
 ('EnsemblesLemmas.lean','acceptProb_coins_fst'):('STAGE2','use TCSlib.Cryptography.acceptProb_def','confirmed'),
 ('EnsemblesLemmas.lean','statClose_of_subsingleton'):('STAGE2','use TCSlib.Cryptography.statClose_iff','confirmed'),
 ('EnsemblesLemmas.lean','distAdv_eq_zero_of_subsingleton'):('STAGE2','use TCSlib.Cryptography.distAdv_def','confirmed'),
 ('EnsemblesLemmas.lean','exists_pushRed'):('STAGE2','use Complexity.NUPPT.coins_ofPolyTime (PPT.lean)','changed reader: the rfl is the coins field of NUPPT.ofPolyTime (a <field>_<def> reader the first index missed)'),
 ('EnsemblesLemmas.lean','acceptProb_multicopyRed_congr'):('STAGE2','use TCSlib.Cryptography.acceptProb_def','confirmed'),
 ('EnsemblesLemmas.lean','exists_copiesRed'):('STAGE2','use Complexity.NUPPT.coins_ofPolyTimeUniform (PPT.lean)','changed reader: the rfl is the coins field of NUPPT.ofPolyTimeUniform'),
 ('Collections.lean','toCollection_sampleClose'):('STAGE2','restate hX through TCSlib.Cryptography.FunFamily.toCollection_decD and toCollection_domEquiv_apply, with toCollection_sample_eq and Complexity.NUPPT.coins_ofPolyTimeUniform for the Coins type (the step reads the D and sample fields of toCollection at the type level)','resolved; type-level field read, needs care in Stage 2'),
 ('Functions.lean','not_hardCore_const'):('STAGE2','use TCSlib.Cryptography.predProb_def (expose the sample space before HardcoreBit.uprob_eq_one_of_forall)','resolved: the stuck Nonempty is the sample space of the sealed predProb'),
 ('Functions.lean','glPad_f'):('STAGE2','use TCSlib.Cryptography.HardcoreBit.glPad_apply','confirmed'),
 ('Functions.lean','glPad_f_bijective'):('STAGE2','use TCSlib.Cryptography.HardcoreBit.glPad_apply','confirmed'),
 ('Functions.lean','glBit_append'):('STAGE2','add TCSlib.Cryptography.HardcoreBit.glBit_eq (glBit (x, r) = ip x r) next to HardcoreBit.glBit','confirmed; no published reader'),
 ('Functions.lean','glPad'):('STAGE2','use TCSlib.Cryptography.FunFamily.glPad_f / glPad_inLen_eval / glPad_outLen_eval with TCSlib.Cryptography.glPadInvMachine_runAt to bridge invProbAt of the padded family','changed reader; needs a check in Stage 2'),
 ('Functions.lean','glPad_hardCore'):('STAGE2','use TCSlib.Cryptography.FunFamily.glPad_f / glPad_inLen_eval / glPad_outLen_eval and invProbAt_eq_uprob to bridge invProbOpt_glFam_eq','changed reader (advInput_eq does not reach the read); needs a check'),
 ('HardCoreCollection.lean','glPad_sample_runAtL'):('STAGE2','use Complexity.NUPPT.uniform_iff (F.sample_uniform is applied to n; the l.175 error is its consequence)','changed reader'),
 ('HardCoreCollection.lean','glPad_hardCore'):('STAGE2','use TCSlib.Cryptography.Collection.hardCore_iff (PermCollection/TrapdoorCollection forms: also oneWay_iff)','confirmed'),
 ('HardCoreGL.lean','orbit_eq'):('STAGE2','add TCSlib.Cryptography.SelXor.input_eq (SelXor.input m β s = pairEncode (pairEncode (List.replicate m true) (List.ofFn β)) (blocksStr s)) next to SelXor.input','confirmed; statement given'),
 ('HardCoreGL.lean','unaryMulFun_poly'):('STAGE2','use Complexity.polyTimeComputable_iff','confirmed'),
 ('HardCoreGL.lean','glMachine_runAt'):('STAGE2','use TCSlib.Cryptography.blocksStr_def / take_drop_blocksStr and TCSlib.Cryptography.glMajFun_blocksStr (the rewrite fails on the sealed blocksStr inside glMajFun)','changed reader'),
 ('HardCoreGL.lean','ofFn_glCoinsEquiv'):('STAGE2','use TCSlib.Cryptography.blocksStr_def and TCSlib.Cryptography.glBlocks_apply (with NUPPT.coinLen_eq for A.Coins)','changed reader'),
 ('HardCoreLemmas.lean','statClose_glPadSampler'):('STAGE2','use Complexity.NUPPT.coinLen_eq','confirmed'),
 ('OneWayYao.lean','length_g_iterate_le'):('STAGE2','use Complexity.NUPPT.inCoins_eq','confirmed'),
 ('OneWayYao.lean','ans_layout'):('STAGE2','use Complexity.NUPPT.runAt_eq','changed reader: the rfl unfolds runAt to output ∘ layout'),
 ('OneWayYao.lean','exists_yaoReduction'):('STAGE2','use Complexity.NUPPT.coinLen_eq with TCSlib.Cryptography.OneWay.YaoMachine.ρP_eval to identify A.Coins n with the sampler coins','changed reader; needs a check'),
 ('Universal.lean','clockedAnswer_eq_cons_of_computesInTime'):('STAGE2-PROVIDER-READER','provider TCSlib/Complexity/TuringMachine/Encoding.lean: add Turing.CodeTM.toFinTM_tm (the tm/State fields of c.toFinTM are c.tm and Fin (c.numStates + 1)); only toFinTM_k is published','changed class: the read is the tm/State field of CodeTM.toFinTM'),
 ('Universal.lean','clockedAnswer_eq_false_of_not_computesInTime'):('STAGE2-PROVIDER-READER','provider TCSlib/Complexity/TuringMachine/Encoding.lean: add Turing.CodeTM.toFinTM_tm (the tm/State fields of c.toFinTM are c.tm and Fin (c.numStates + 1)); only toFinTM_k is published','changed class: the read is the tm/State field of CodeTM.toFinTM'),
 ('Universal.lean','ofFn_getD_eq_take'):('STAGE2','use TCSlib.Cryptography.padFin_def','confirmed'),
 ('Universal.lean','invProbAt_reduction_ge'):('STAGE2','use TCSlib.Cryptography.fUniversal_inLen_eval (cast e (w.1, w.2.1) along it)','resolved'),
 ('UniversalPadding.lean','invProbAt_family_le'):('STAGE2','use Complexity.NUPPT.coinLen_eq','confirmed'),
 ('UniversalPadding.lean','exists_family'):('STAGE2','use TCSlib.Cryptography.PadQuad.family_inLen (the step reads the inLen field of family)','changed reader'),
 ('UniversalLemmas.lean','exists_reparam_pre_post'):('STAGE2','use Complexity.NUPPT.coins_ofPolyTime (PPT.lean)','changed: a published <field>_<def> reader exists'),
 ('UniversalLemmas.lean','exists_reparam_pre_post_adv'):('STAGE2','use Complexity.NUPPT.coins_ofPolyTime (PPT.lean)','changed: a published <field>_<def> reader exists'),
 ('GoldreichLevinDomain.lean','invProb_guessInverter_enc'):('STAGE2','use TCSlib.Cryptography.HardcoreBit.secProb_def and TCSlib.Cryptography.uexp_def','confirmed'),
 ('SamplingFinDist.lean','statClose_iff_epsClose_map'):('STAGE2','use TCSlib.Cryptography.statClose_iff','confirmed'),
 ('InnerProduct.lean','uprob_recover_le_invProb'):('STAGE2','use TCSlib.Cryptography.invProb_def (expose the sample space before uprob_mono)','resolved'),
 ('InnerProduct.lean','invProb_perfectInverter'):('STAGE2','use TCSlib.Cryptography.predProb_def and TCSlib.Cryptography.invProb_def','confirmed (the error sits at `by`, not in the statement)'),
 ('IterateFind.lean','polyTimeComputable_find'):('STAGE2','F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it','changed fix text'),
 ('IterateFind.lean','computesFunInTime_find'):('STAGE2','F-01, cleared by #347 (pending). The read is the State field of the host machine H (`.inl 0 : H.State`); hostCtrl_eq does not give it','changed fix text'),
 ('ModuleHost.lean','stop_step'):('STAGE2',APPLY,'refined: all apply fields'),
 ('ModuleHost.lean','stop_clean'):('STAGE2','use Turing.MultiTapeTM.runFrom_zero (zero case), then Turing.Cfg.ofWords_def and Turing.stateWord_eq','refined'),
 ('ModuleHost.lean','clean_install'):('STAGE2','use Complexity.polyTimeComputable_iff','confirmed'),
 ('ModuleHost.lean','clean_emit'):('STAGE2','use Complexity.polyTimeComputable_iff','confirmed'),
 ('ModuleHost.lean','pad_apply'):('STAGE2',APPLY,'refined'),
 ('ModuleHost.lean','pad_run'):('STAGE2',APPLY,'refined'),
 ('ModuleHost.lean','pad_seam'):('STAGE2','use Turing.Cfg.ofWords_def and Turing.stateWord_eq','confirmed'),
 ('ModuleHost.lean','host_seam'):('STAGE2','use Turing.Cfg.ofWords_def and Turing.stateWord_eq','confirmed'),
 ('ModuleHost.lean','host_call'):('STAGE2','use Turing.Cfg.ofWords_def and Turing.stateWord_eq','confirmed'),
 ('IterateFindHost.lean','copy_clean'):('STAGE2','use Turing.Cfg.ofWords_def and Turing.stateWord_eq','confirmed'),
 ('IterateFindHost.lean','copy_finish'):('STAGE2',APPLY,'refined'),
 ('IterateFindHost.lean','copy_rewind'):('STAGE2',APPLY,'refined'),
 ('IterateFindHost.lean','copy_step'):('STAGE2',APPLY,'refined'),
 ('IterateFindHost.lean','copy_turn'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','split_copy'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','split_run'):('STAGE2',RUNCH,'changed reader: the change reads runFrom'),
 ('PairSplit.lean','split_sep'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','split_tail'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','apply_cfg_advance'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','apply_cfg_stay'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','cfg_workTapeSymbols'):('STAGE2','use Turing.Cfg.workTapeSymbols_eq and Turing.FinTM.bufferTape_eq','confirmed'),
 ('PairSplit.lean','parse_block'):('STAGE2',RUNCH,'changed reader'),
 ('PairSplit.lean','parse_first'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','rewind_run'):('STAGE2',APPLY,'refined'),
 ('UnaryMul.lean','exists_unaryMulTM'):('STAGE2','use Turing.FinTM.computesFunInTime_iff','confirmed'),
 ('UnaryMul.lean','mul_back'):('STAGE2','give the private unaryMulTM field equations (unaryMulTM.k = 1, unaryMulTM.State = MulControl) or state mul_tr_back for a MultiTapeTM 1 Bool MulControl that unaryMulTM wraps, in UnaryMul.lean: the read is the k/State field (Fin 1 against Fin unaryMulTM.k)','resolved; refactor of a private def, needs a check'),
 ('UnaryMul.lean','mul_run'):('STAGE2',RUNCH,'changed reader'),
 ('Primitives.lean','polyTimeComputable_unaryMulFun'):('STAGE2','use Complexity.polyTimeComputable_iff','confirmed'),
 ('Primitives.lean','computesFunInTime_unaryMul'):('STAGE2','use Turing.FinTM.computesFunInTime_iff and state both sides through one function (two different `match pairDecode z` terms meet; reading pairDecode is not needed)','changed reader; needs a check'),
 ('Primality.lean','exists_samplePrime_nuppt'):('STAGE2','use Complexity.NUPPT.runAtL_ofPolyTimeUniform / output_ofPolyTimeUniform (PPT.lean) to compute the sampler run','changed reader; needs a check'),
 ('LeftoverHash.lean','collision_hashPair_le'):('STAGE2','use TCSlib.InformationTheory.isUniversal_iff (hf is applied as a function) and TCSlib.InformationTheory.FinDist.collision_def','changed reader'),
 ('Chebyshev.lean','uprob_prime_bits'):('STAGE2','use TCSlib.Cryptography.bitsEquiv_val (published; the first index missed it)','changed: published reader'),
 ('Entropy.lean','isSource'):('STAGE2','use TCSlib.InformationTheory.FinDist.hasMinEntropy_iff','resolved'),
 ('Entropy.lean','isSource_uniform'):('STAGE2','use TCSlib.InformationTheory.FinDist.hasMinEntropy_iff','confirmed'),
 ('Entropy.lean','le_minEntropy_iff'):('STAGE2','use TCSlib.InformationTheory.FinDist.hasMinEntropy_iff','resolved'),
}
P = {  # scan (unfold/eqn) items: (file suffix, provider) -> (class, fix, note)
 ('IterateFindHost.lean','Turing.Action.apply'):('STAGE2',APPLY,'refined'),
 ('PairSplit.lean','Turing.Action.apply'):('STAGE2',APPLY,'refined'),
 ('IterateFindHost.lean','Turing.MultiTapeTM.step'):('STAGE2',STEPOF,'changed reader: `unfold MultiTapeTM.step` is read by step_of_some'),
 ('PairSplit.lean','Turing.MultiTapeTM.step'):('STAGE2',STEPOF,'changed reader'),
 ('PairSplit.lean','Turing.Cfg.init'):('STAGE2',INIT,'refined'),
 ('PairSplit.lean','Turing.MultiTapeTM.initCfg'):('STAGE2',INIT,'refined'),
 ('UnaryMul.lean','Turing.Cfg.init'):('STAGE2',INIT,'refined'),
 ('UnaryMul.lean','Turing.MultiTapeTM.initCfg'):('STAGE2',INIT,'refined'),
 ('PairSplit.lean','Turing.pairDecode'):('STAGE2-PROVIDER-READER',PD,'changed class: pairDecode_nil covers one case only'),
 ('UnaryMul.lean','Turing.pairDecode'):('STAGE2-PROVIDER-READER',PD,'changed class: pairDecode_nil covers one case only'),
 ('IterateFindHost.lean','Turing.Cfg.inputSymbol'):('STAGE2','use Turing.Cfg.inputSymbol_of_zero (Configuration.lean; the configuration is at input position 0)','changed class: a published case lemma covers the read'),
 ('PairSplit.lean','Turing.Cfg.inputSymbol'):('STAGE2','use Turing.Cfg.inputSymbol_of_end (Configuration.lean; the read is at the end position i = x.length)','changed class: a published case lemma covers the read'),
 ('PairSplit.lean','Turing.dbl'):('STAGE2','use Turing.dbl_nil and Turing.dbl_cons','refined (both cases)'),
}
COMPLETE={'Turing.Cfg.ofWords','Turing.stateWord','Turing.Cfg.workTapeSymbols','Turing.FinTM.bufferTape',
 'Complexity.P','TCSlib.Cryptography.uexp','TCSlib.InformationTheory.FinDist.probTrue','TCSlib.InformationTheory.FinDist.collision'}
out=[]; un=[]
for r in rows:
    f=r['base_path'].split('/')[-1]; d=r['declaration'].split('.')[-1]
    cl,stl,fx=r['class'],r['statement_level'],r['fix']
    note=None
    if r['channel']=='seal' and cl in ('STAGE2','STAGE2-PROVIDER-READER'):
        v=D.get((f,d))
        if f=='HardCoreCollection.lean' and '.PermCollection.OneWay.' in r['declaration']:
            v=('STAGE2','use TCSlib.Cryptography.PermCollection.oneWay_iff (h : P.OneWay is passed where Collection.OneWay of P.toCollection is expected)','resolved')
        if f=='HardCoreCollection.lean' and '.TrapdoorCollection.OneWay.' in r['declaration']:
            v=('STAGE2','use TCSlib.Cryptography.TrapdoorCollection.oneWay_iff (h : T.OneWay is passed where Collection.OneWay of the underlying collection is expected)','resolved')
        if v: cl,fx,note=v; stl='no'
    elif r['channel']!='seal' and cl in ('STAGE2','STAGE2-PROVIDER-READER'):
        m=re.match(r'(\d+) \S+ (\S+)',r['scan'] if r['scan']!='-' else r['record'])
        prov=m.group(2) if m else None
        v=P.get((f,prov))
        if v: cl,fx,note=v
        elif prov in COMPLETE: note='confirmed (a complete equation reader of '+prov+')'
    if note is None:
        if cl in ('SEAL-B-ONLY','STRICT-ONLY (notation, no fix)','STATEMENT'): note='confirmed (counts; statement range by the tool)'
        else: note='kept tool reader (inspected by group, not re-derived)'; un.append(r['key'])
    out.append([r['key'],cl,stl,fx,'lead: '+note])
w=open(sys.argv[1],'w',encoding='utf-8'); w.write('key\tclass\tstatement_level\tfix\tnote\n')
for x in out: w.write('\t'.join(str(v).replace('\t',' ').replace('\n',' ') for v in x)+'\n')
import collections
print(len(out),'rows; changed class:',collections.Counter((r['class'],x[1]) for r,x in zip(rows,out) if r['class']!=x[1]),'; kept-uninspected',len(un))
for k in un: print('  kept:',k[:150])
