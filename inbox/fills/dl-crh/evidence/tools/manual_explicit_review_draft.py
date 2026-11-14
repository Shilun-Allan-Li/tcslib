#!/usr/bin/env python3
"""Materialize the source-reviewed, row-indexed explicit-list draft; no Lean."""
from collections import Counter
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
PLAN = ROOT / "evidence/probes/Rule10/final1/final-scan-plan.json"
plan_bytes = PLAN.read_bytes()
plan = json.loads(plan_bytes)

# These are manual source dispositions, keyed by stable 1-based inventory row.
# In particular, do not trust the scanner's broad local_names lexical heuristic.
LOCAL_EQUATIONS = {
    2: "ha: length equality obtained by destructing WellFormedIndex through its local proof",
    4: "ha: first numeral length from the obtain pattern",
    5: "hb: second numeral length from the obtain pattern",
    6: "hc: third numeral length from the obtain pattern",
    13: "hl: local encoded-exponent numeral value equality",
    16: "hl: same local numeral value equality, nested rewrite occurrence",
    30: "hl: local numeral readback equality in expEval_spec",
    37: "h1: local equality of modular powers extracted from encoded words",
    54: "h3: local computation dlP dlDefaultIndex = 3",
    55: "h2: local computation dlM dlDefaultIndex = 2",
    56: "h2: same local group-order computation",
    57: "h3: same local prime computation",
    58: "hg: local computation dlG dlDefaultIndex = 2",
    59: "hg: same local generator computation",
    60: "h3: same local prime computation",
    61: "hg: same local generator computation",
    62: "h2: same local group-order computation",
    63: "h3: same local prime computation",
    93: "hacc: local acceptance-probability equality in sampler proof",
    115: "he: equation g z = [] supplied by split_ifs, omitted by lexical local_names",
    130: "hvdef: equation supplied by set v := ... with hvdef, omitted by lexical local_names",
    131: "hs: local case equation for sampleBelowL, omitted by lexical local_names",
    133: "hvdef: same local set-definition equation",
    134: "hs: local some-branch sampler equation",
    139: "henc: local identification of a numeral with an exponent encoding",
    141: "henc: same local encoding identification",
    155: "hofn: locally proved equality of coin words under the coin equivalence",
    159: "hX: local equality of sampled functions in dla_statClose_expDec",
    160: "hY: local equality of ideal functions in dla_statClose_expDec",
    170: "hY: local ideal-decoder function equality in expCollection_sampleClose",
    172: "hw: hypothesis dlW i = n, a proof of equality, not a local let",
    199: "heq: local arithmetic equality a+b+(m-b) = a+m",
    210: "hxval: local bounded cast has representative x",
    211: "hxval': local bounded cast has representative x'",
    212: "hnum: local equality of generator-power residue values",
    213: "hxval: same local bounded-cast representative equality",
    214: "hxval': same local bounded-cast representative equality",
    230: "hfst: local function equality derived by funext from splitBits_fst",
    233: "hsnd: local function equality derived by funext from splitBits_snd",
    248: "hprefix: argument asserting equality of the two prefix words",
    249: "hlast: argument asserting equality of the selector bits",
    254: "hxlen: locally proved length of x's prefix",
    255: "hylen: locally proved length of y's prefix",
    256: "hxcanon: public numeral canonicity instantiated locally on x's prefix",
    257: "hycanon: public numeral canonicity instantiated locally on y's prefix",
    262: "hlen: local exact prefix length in boundedInputEquiv inverse law",
    263: "hcanon: local instance of numeral canonicity in boundedInputEquiv",
    333: "hlen: local exact length of the concatenated domain words",
    343: "he: local representation equation from wellFormedIndex_iff obtain pattern",
    350: "hpad: locally proved identity of padding an exact-length word",
    351: "hfirst: locally proved first-prefix cut equality",
    352: "hsecond: locally proved second-prefix cut equality",
    353: "hselector: locally proved selector extraction equality",
    355: "hmw: local equality of the encoded order word's length and n",
    368: "hsplit: local concatenation equality for splitBits' encoded components",
    369: "hword: locally instantiated public padding/word equation",
    375: "hidem: local padding idempotence equation proved via public padding readers",
    424: "hs: local none-branch sampler equation from cases, omitted by lexical local_names",
    427: "hs: local some-branch sampler equation from cases, omitted by lexical local_names",
    435: "hz: local representative equality z.val = w",
    444: "he: local encoding of the bounded exponent equals its prefix word",
    455: "he: local index representation equation obtained through wellFormedIndex_iff",
    465: "hw': local prime-numeral width equality, not a definition",
    539: "hkey: local generated-key equation from obtain on dlHashGenFun_key",
    555: "hmfull: local consequence of hV asserting m = p-1",
    577: "hanswer: local equality of reduction output with natToList n z.val",
}
LOCAL_LETS = {
    325: "width: local PolyExpr for two (n+1)-bit blocks in collisionPost_ofFn_append",
    337: "width: same local PolyExpr, explicitly dsimp-reduced",
    360: "width: local PolyExpr for two (n+1)-bit blocks in collisionPost_split",
    361: "u: local let List.replicate n true in collisionPost_split",
    370: "width: same local PolyExpr, dsimp-reduced in hidem",
    371: "width: same local PolyExpr, dsimp-reduced in the target",
    423: "w: local let defining the sampler result with fallback zero",
    426: "w: same local sampler-result let in the some branch",
}
DOT_THEOREM_ROWS = {398, 437, 446, 457, 477, 480, 491, 494, 540, 573, 580, 588}
FALSE_LOCAL_ROWS = {153: "ZMod.val_natCast", 197: "ZMod.val_natCast", 488: "ZMod.val_mul"}

OWN_DEFINITIONS = set("""
dlW expOrd expDec expEnc expEval expF dlG dlP dlM dlProb dlDefaultIndex expGenFun
expGen sampleBelowL dla_belowAcc expSampleRaw expSampler dlHashGenFun dlHashMul dlHashPow
""".split())
CORE_MATHLIB_EQUATIONS = set("""
Bool.false_eq_true Equiv.apply_symm_apply Equiv.arrowCongr_symm Equiv.prodCongr_apply
Equiv.prodCongr_symm Equiv.refl_apply Equiv.refl_symm Equiv.symm_apply_apply
Equiv.symm_symm Equiv.symm_trans_apply Fintype.card_bool Fintype.card_congr Fintype.card_fin
Fintype.card_prod Function.comp_apply List.append_nil List.concat_eq_append
List.drop_append_of_le_length List.drop_left' List.drop_zero List.findSome?_eq_some_iff
List.headD_cons List.length_append List.length_drop List.length_ofFn List.length_replicate
List.length_take List.ofFn_congr List.ofFn_get List.ofFn_succ' List.replicate_zero
List.tail_nil List.take_append_drop List.take_left' List.take_of_length_le
Nat.add_mod_right Nat.add_sub_cancel_left Nat.cast_pow Nat.min_eq_left Nat.mod_eq_of_lt
Nat.mul_comm Nat.not_le Nat.sub_add_cancel Nat.sub_self Nat.zero_add Option.getD_none
Option.getD_some Option.map_some Option.some.inj Option.some.injEq Prod.map_fst Prod.map_snd
Units.val_mul Units.val_pow_eq_pow_val ZMod.natCast_mod ZMod.natCast_zmod_val ZMod.val_mul
ZMod.val_natCast abs_of_nonneg abs_zero decide_eq_decide decide_eq_true_eq decide_not dif_pos
finCongr_symm if_neg if_pos inv_mul_eq_div one_div one_mul orderOf_units pow_add
""".split())
TCSLIB_READERS = set("""
CRH.collisionGame_eq CRH.collisionResistant_iff CRH.compresses_iff CRH.hash_eq
Collection.index_eq Collection.invProbAt_eq Collection.sampleClose_iff ExpGroupGen.dlProb_eq
FromDiscreteLog.card_boundedInput FromDiscreteLog.card_boundedRange FromDiscreteLog.collisionPost_split
FromDiscreteLog.collision_accept_eq FromDiscreteLog.expEval_natToList_val FromDiscreteLog.expUnit_pow_val
FromDiscreteLog.inputWord_drop FromDiscreteLog.sumCoinsEquiv_symm_ofFn HardcoreBit.uexp_add
HardcoreBit.uexp_comp_equiv HardcoreBit.uexp_const HardcoreBit.uexp_prod
NUPPT.Uniform.runAtL_eq NUPPT.Uniform.runAt_eq NUPPT.advInput_eq NUPPT.adv_ofPolyTime
NUPPT.advice_ofPolyTime NUPPT.coinLen_eq NUPPT.coinsCongr_ofFn NUPPT.coinsEquivPoly_ofFn
NUPPT.coinsEquivPoly_symm_ofFn NUPPT.coins_ofPolyTime NUPPT.coins_ofPolyTimeUniform
NUPPT.inArg_eq NUPPT.inArg_layout NUPPT.inCoins_eq NUPPT.inCoins_layout NUPPT.inParam_eq
NUPPT.inParam_layout NUPPT.layout_eq NUPPT.runAtL_eq NUPPT.runAtL_ofPolyTime
NUPPT.runAtL_ofPolyTimeUniform NUPPT.runAt_eq PolyExpr.eval_add PolyExpr.eval_const
PolyExpr.eval_mul PolyExpr.eval_var ProbComp.expect_sample ProbComp.prob_bind ProbComp.prob_pure
accept_eq atParam_eq bitsEquiv_val bitsToNat_eq_listToNat bitsToNat_natToBits coe_expUnit
collisionPost_eq collisionReduction_eq collisionReduction_runAtL decodeFin_eq decodeFin_ofFn
divModStr_pairEncode dlHashCollision_iff dlHashEval_atParam dlHashEval_eq dlHashEval_expF
dlHashGenFun_eq dlHashGenFun_layout dlHashIdx_eq dlHashIdx_layout dlHashMul_atParam
dlHashMul_eq dlHashPow_atParam dlHashPow_eq dlHash_coinsEquiv_eq dlHash_coinsEquiv_symm_ofFn
dlHash_collision_accept_eq dlHash_domLen dlHash_eval dlHash_gen dlHash_gen_runAt dlHash_inDom
dlHash_inRange dlHash_rangeLen dlM_eq dlP_eq expCollection_decD expCollection_f expCollection_index
expCollection_sample expDec_expEnc expEnc_eq expEval_spec expF_eq expGenFun_eq expGen_coins
expGen_coinsEquiv_ofFn expGen_runAt expOrd_of_valid expSampleRaw_eq expSampler_runAt
expUnit_pow_val expect_sample_eq_uexp inputWord_drop inputWord_split inputWord_take
length_natToList length_pairEncode length_sizeStr listToNat_addStr listToNat_mulStr
listToNat_natToList listToNat_nil listToNat_subStr modExpStr_pairEncode modularDifference_eq
modularDifference_value natToBits_bitsToNat natToList_eq natToList_val_natCast
natToList_zero_append_drop ofFn_arrowCongr_finCongr ofFn_padFin_eq_padStr ofFn_padFin_of_length
ofFn_splitBits_fst ofFn_splitBits_snd ofFn_splitCoins_symm orderOf_expUnit padFin_ofFn
padStr_of_length_le pairFstD_pairEncode pairSndD_pairEncode reductionRaw_eq rejectBlocksL_eq
residueFinEquiv_val sampleBelowL_eq_rejectBlocksL subStr_pairEncode sumCoinsEquiv_eq uexp_def
uprob_comp_equiv uprob_eq_uexp uprob_false uprob_prod uprob_rejectionSample_none val_units_pow
""".split())

rows = []
for index, item in enumerate(plan["items"], 1):
    head = item["head"]
    row = {"row_id": index, "head": head, "declaration_status": item["declaration_status"]}
    if index in LOCAL_EQUATIONS:
        row.update(draft_class="LOCAL_PROOF_EQUATION", reason=LOCAL_EQUATIONS[index],
                   expected_kind="local proof term", draft_disposition="SOURCE_SCOPE_REVIEWED")
    elif index in LOCAL_LETS:
        row.update(draft_class="LOCAL_LET_BODY", reason=LOCAL_LETS[index],
                   expected_kind="local let", draft_disposition="SOURCE_SCOPE_REVIEWED")
    elif index in DOT_THEOREM_ROWS:
        assert head == "hw.dlW_eq"
        row.update(draft_class="PUBLISHED_THEOREM_DOT_NOTATION",
                   expected_symbol="TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq",
                   expected_kind="theorem",
                   reason="hw has type WellFormedIndex n i; .dlW_eq is its published theorem, not an arbitrary local projection",
                   draft_disposition="PENDING_NATIVE_KIND_HOME")
    elif index == 114:
        assert head == "show"
        row.update(draft_class="INLINE_EQUATION_PROOF", expected_kind="term syntax",
                   reason="the item is a typed show-equality proof supplied by (hs z).2 from the public rejectBlocksL contract; show is not a constant to unfold",
                   draft_disposition="SOURCE_SCOPE_REVIEWED")
    elif head == "reduceIte":
        assert item["item"] == "↓reduceIte"
        row.update(draft_class="BUILTIN_SIMPLIFIER_CONTROL", expected_kind="simp directive",
                   reason="↓reduceIte is the simplifier's built-in conditional-reduction control, not a named foreign definition",
                   draft_disposition="SOURCE_SYNTAX_REVIEWED")
    elif head in OWN_DEFINITIONS:
        row.update(draft_class="SAME_FILE_DEFINITION", expected_kind="def",
                   expected_home=item["module"],
                   reason=f"{head} is declared in the file containing this unchanged declaration; same-file definition reading is permitted and preserved at base",
                   draft_disposition="PENDING_NATIVE_KIND_HOME")
        assert item["declaration_status"] == "SAME"
    elif head in CORE_MATHLIB_EQUATIONS:
        row.update(draft_class="CORE_MATHLIB_EQUATION_CANDIDATE", expected_kind="theorem",
                   reason=f"the explicitly named item is the {head} equation/injectivity/cardinality law, not the body of its related core/Mathlib definition",
                   draft_disposition="PENDING_NATIVE_KIND_HOME")
    elif head in TCSLIB_READERS:
        row.update(draft_class="TCSLIB_PUBLIC_READER_CANDIDATE", expected_kind="theorem",
                   reason=f"{head} is the named public equation, field/contract, or predicate-characterization theorem used at this source location",
                   draft_disposition="PENDING_NATIVE_KIND_HOME")
    else:
        raise RuntimeError(f"No manual source disposition for row {index}: {head}")
    if index in FALSE_LOCAL_ROWS:
        assert head == FALSE_LOCAL_ROWS[index]
        row["lexical_correction"] = "ZMod was falsely captured from a type expression as a binder; this item denotes the global theorem named by the qualified token"
    if index in LOCAL_EQUATIONS and head.split(".", 1)[0] not in item["local_names"]:
        row["lexical_correction"] = "actual source equation binder omitted by local_names; see the recorded obtain/cases/set binding"
    row["final_native_disposition"] = "NOT_YET_REVIEWED"
    rows.append(row)

assert len(rows) == 595
result = {
    "status": "DRAFT_SOURCE_REVIEW_NATIVE_KIND_HOME_PENDING",
    "plan": str(PLAN.relative_to(ROOT)),
    "plan_sha256": hashlib.sha256(plan_bytes).hexdigest(),
    "review_method": "All 595 inventory items were manually read in declaration groups; exact row overrides distinguish local proof equations, local lets, dot-notation theorems, parser syntax, and named globals. The script materializes that manual source review; it does not clear native definition candidates.",
    "status_counts": dict(Counter(row["declaration_status"] for row in rows)),
    "draft_class_counts": dict(Counter(row["draft_class"] for row in rows)),
    "native_work_remaining": "Join every row with the later native scan. For each def candidate, record its fully qualified name/home/kind and same-file or foreign disposition, including Core/Mathlib. Resolve every ambiguous/unresolved/global-local conflict manually. No final clearance is issued by this draft.",
    "rows": rows,
}
print(json.dumps(result, ensure_ascii=False, separators=(",", ":")))
