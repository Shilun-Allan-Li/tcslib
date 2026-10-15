import json, re
rows = json.load(open('mrows.json')); cons = {(c['home'], c['line']): c for c in json.load(open('consumers.json'))}
wit = {
 'computesFunInTime_id': '`idTM` (P, Composition:88)', 'computesFunInTime_const': '`constTM` (P, Composition:168)',
 'computesFunInTime_ifEq': '`ifEqTM` (P, Composition:189)', 'computesFunInTime_comp': '`bufferedCompTM` (public, Simulation:618)',
 'exists_comp_on_image': '`bufferedCompTM` (public)', 'exists_comp_partial': '`bufferedCompTM` (public)',
 'exists_cond': '`condTM` (P, Composition:517)', 'computesFunInTime_cond': '`timedCondTM` (P, Wrappers:479)',
 'computesFunInTime_prepend': '`catalogPrefixTM` (P, Primitives:129)', 'computesFunInTime_lengthBits': '`Complexity.counterTM` (P, TimeConstructible:130), through `timeConstructible_id`',
 'computesFunInTime_polyUnary': '`constTM` / `catalogPolyUnaryTM` (P, Primitives:1009), split on `e`', 'computesFunInTime_polyBits': 'existential composite (`computesFunInTime_comp` of two rows)',
 'computesFunInTime_pairEncodeFixed': 'the prepend row at a fixed word', 'computesFunInTime_pairFst': '`pairExtractTM true false` (P, Primitives:665)',
 'computesFunInTime_pairSnd': '`pairExtractTM false true`', 'computesFunInTime_pairValid': '`pairValidTM` (P, Primitives:569)',
 'computesFunInTime_pairConcat': '`pairExtractTM true true`', 'computesFunInTime_pairDup': '`pairDupTM` (P, Primitives:271)',
 'computesFunInTime_pairMapSnd': '`pairMapTM (bufferedCompTM (pairExtractTM false true) Mg)` (P, Primitives:2297)',
 'computesFunInTime_pairLenCheck': '`pairCountTM G` (P, Primitives:1417), `G` an existential composite', 'computesFunInTime_stripLast': 'existential (`computesFunInTime_cond` over `rawStripTM`, `anyTrueTM`)',
 'computesFunInTime_splitSolve': '`splitSolve_closed` (P): `exists_loopFindTM` over `splitBodyTM`', 'computesFunInTime_incFixed': '`incFixedTM` (P, Primitives:460)',
 'computesFunInTime_splitSolveWith': '`emitterP2_closed` (P): two `exists_installCallTM`, a loop', 'computesFunInTime_unaryToken': '`emitterTokenTM` (P, Primitives:6087)',
 'computesFunInTime_appendBit': '`emitterAppendTM b` (P, Primitives:6252)', 'exists_loopCfgTM': '`loopHost _ _ _ false` (P abbrev, Loop:649)',
 'exists_loopTM': 'through `exists_loopCfgTM` (`loopHost`)', 'exists_loopFindTM': '`loopHost _ _ _ true`', 'exists_emitLoopTM': '`emLoopHost` (P abbrev, Loop:4623)',
 'exists_installCallTM': '`emCallTM M false`, `q₀`, `.inr (.inr 5)` (P, Loop:3897)', 'exists_emitCallTM': '`emCallTM M true`, same states',
 'computesFunInTime_pairEncode_diag': '`pairDiagTM` (P, Encoding:299)', 'exists_codeTM': 'anonymous `⟨card Q − 1, tm.relabelState e⟩`',
 'computesFunInTime_id_spaceUsed': '`f2_idTM`', 'computesFunInTime_const_spaceUsed': '`f2_constTM`',
 'computesFunInTime_prepend_spaceUsed': '`f2_catalogPrefixTM`', 'computesFunInTime_lengthBits_spaceUsed': '`f2_counterTM`',
 'computesFunInTime_polyUnary_spaceUsed': 'const row / `f2_catalogPolyUnaryTM`', 'computesFunInTime_polyBits_spaceUsed': 'const row / `bufferedCompTM f2_catalogPolyUnaryTM f2_counterTM`',
 'computesFunInTime_pairEncodeFixed_spaceUsed': 'the prepend space row', 'computesFunInTime_pairFst_spaceUsed': '`f2_pairExtractTM`',
 'computesFunInTime_pairSnd_spaceUsed': '`f2_pairExtractTM`', 'computesFunInTime_pairValid_spaceUsed': '`f2_pairValidTM`',
 'computesFunInTime_pairConcat_spaceUsed': '`f2_pairExtractTM`', 'computesFunInTime_pairDup_spaceUsed': '`f2_pairDupTM`',
 'computesFunInTime_pairLenCheck_spaceUsed': '`f2_pairCountTM` over a buffered composite', 'computesFunInTime_stripLast_spaceUsed': 'existential (`f2_strip_linear`, through `computesFunInTime_cond`)',
 'computesFunInTime_incFixed_spaceUsed': '`f2_incFixedTM`', 'computesFunInTime_pairMapSnd_spaceUsed': '`a2_mapTM Mg true` (new, not a copy)',
 'computesFunInTime_splitSolve_spaceUsed': '`f2_splitSolve_closed` (`f2_loopHost` over `f2_splitBodyTM`)', 'computesFunInTime_cond_spaceUsed': '`f2_timedCondTM`',
 'exists_loopTM_spaceUsed': '`f2_loopHost`',
}
out = []
for o in rows:
    c = cons[('TCSlib/' + o['file'], o['line'])]
    f = o['file'].split('/')[-1][:-5]
    shape = ' '.join(o['concl'].split())
    shape = re.sub(r'\(x : List Bool\) \(t : ℕ\)', 'x t', shape)
    if len(shape) > 140: shape = shape[:137] + '…'
    shape = shape.replace('|', '\\|')
    ext = ', '.join(f"{k.split('/')[-1][:-5]} {v}" for k, v in sorted(c['ext'].items()))
    out.append(f"| {f}:{o['line']} | `{o['name']}` | `{shape}` | {wit[o['name']]} | {c['internal']} | {c['ext_cites']} / {c['ext_files']} | {ext or '—'} | {c['doc']} |")
open('rows_table.md', 'w').write('\n'.join(out) + '\n')
print(len(out))
