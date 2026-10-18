import json, re, sys, glob
root = sys.argv[1]
idx = json.load(open('fullnames.json'))
proposed = {
 'Turing.FinTM.idTM': 'Composition', 'Turing.FinTM.constTM': 'Composition', 'Turing.FinTM.ifEqTM': 'Composition',
 'Turing.FinTM.condTM': 'Composition', 'Turing.FinTM.timedCondTM': 'Wrappers', 'Turing.FinTM.prependTM': 'Primitives',
 'Turing.FinTM.lengthBitsTM': 'TimeConstructible', 'Turing.FinTM.polyUnaryTM': 'Primitives',
 'Turing.FinTM.polyBitsTM': 'Primitives', 'Turing.FinTM.pairExtractTM': 'Primitives', 'Turing.FinTM.pairValidTM': 'Primitives',
 'Turing.pairDiagTM': 'Encoding', 'Turing.FinTM.pairMapSndTM': 'Primitives', 'Turing.FinTM.pairLenCheckTM': 'Primitives',
 'Turing.FinTM.stripLastTM': 'Primitives', 'Turing.FinTM.splitSolveTM': 'Primitives', 'Turing.FinTM.incFixedTM': 'Primitives',
 'Turing.FinTM.splitSolveWithTM': 'Primitives', 'Turing.FinTM.unaryTokenTM': 'Primitives', 'Turing.FinTM.appendBitTM': 'Primitives',
 'Turing.FinTM.toCodeTM': 'Encoding', 'Turing.FinTM.loopHostTM': 'Loop', 'Turing.FinTM.emitLoopTM': 'Loop',
 'Turing.FinTM.callTM': 'Loop', 'Turing.FinTM.callExit': 'Loop',
 'Turing.FinTM.polyUnaryEngineTM': 'Primitives',
 'Turing.FinTM.ComputesInTime.spaceUsed_le': 'Catalog',
}
specs = ['idTM_computes', 'constTM_computes', 'ifEqTM_computes', 'condTM_computes', 'timedCondTM_computes', 'timedCondTM_spaceUsed',
 'prependTM_computes', 'lengthBitsTM_computes', 'lengthBitsTM_spaceUsed', 'polyUnaryTM_computes', 'polyUnaryTM_spaceUsed',
 'polyBitsTM_computes', 'pairExtractTM_computes', 'pairValidTM_computes', 'pairDiagTM_computes', 'pairMapSndTM_computes',
 'pairMapSndTM_spaceUsed', 'pairLenCheckTM_computes', 'stripLastTM_computes', 'splitSolveTM_computes', 'splitSolveTM_spaceUsed',
 'incFixedTM_computes', 'splitSolveWithTM_computes', 'unaryTokenTM_computes', 'appendBitTM_computes', 'toCodeTM_computesInTime_iff',
 'loopHostTM_contracts', 'loopHostTM_spaceUsed', 'emitLoopTM_computes', 'callTM_install', 'callTM_emit', 'callTM_k_pos',
 'bufferedCompTM_computesFunInTime', 'redirectTM_runFrom', 'polyUnaryTM_computes_sharp', 'prependTM_k', 'idTM_k']
for s in specs:
    proposed.setdefault('Turing.FinTM.' + s, '?')
# 1. exact full-name clashes, and same-short-name declarations anywhere
for full, home in proposed.items():
    short = full.split('.')[-1]
    ex = [d for d in idx if d['full'] == full]
    same = [d for d in idx if d['short'] == short and d['full'] != full]
    if ex or same:
        print(full, '| exact:', [(d['file'].split('TCSlib/')[-1], d['line'], 'P' if d['private'] else 'PUB') for d in ex],
              '| same short name:', [(d['full'], d['file'].split('/')[-1], d['line'], 'P' if d['private'] else 'PUB') for d in same][:6])
print('---- bare uses in colleague files that open Turing.FinTM or sit in it')
col = ['TCSlib/Complexity/TimeHierarchy/Separation.lean'] + sorted(glob.glob(root + '/TCSlib/Complexity/CircuitComplexity/*.lean'))
for f in col:
    p = f if f.startswith('/') else root + '/' + f
    s = open(p, encoding='utf-8').read()
    for full in proposed:
        short = full.split('.')[-1]
        for pref in ['', 'FinTM.']:
            pat = re.compile(r'(?<![\w.\'])' + re.escape(pref + short) + r'(?![\w\'])')
            n = len(pat.findall(s))
            if n: print(p.split('TCSlib/')[-1], repr(pref + short), n)
