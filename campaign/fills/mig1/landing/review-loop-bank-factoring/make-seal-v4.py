"""Instrument the four complete proof declarations, before docstrings and headers."""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
source = (OUT / 'Loop-cumulative-proposed-v2.lean.txt').read_text()
prior = ROOT / 'campaign/fills/mig1/landing/review-composition-loop'
definitions = (prior / 'control-definitions.txt').read_text().splitlines() + ['Turing.FinTM.tapeBlocks']
assert len(definitions) == len(set(definitions)) == 31
names = ['loop_computes_of_startup', 'loopHostTM_decides', 'loopHostTM_finds',
         'emitLoopTM_computes', 'emCall_bank_embed', 'emCall_bank_initial', 'emCall_bank_final']
regions = []
instrumentation = []
for name in names:
    m = re.search(r'(?m)^(?:private )?(?:lemma|theorem) ' + name + r'(?=\s|\()', source)
    assert m, name
    start = source.rfind('/--', 0, m.start())
    end = source.index('\n/--', m.end()) + 1
    assert start >= 0 and start < m.start()
    regions.append(dict(name=name, start=start, end=end,
                        first_line=source.count('\n', 0, start) + 1,
                        last_line=source.count('\n', 0, end),
                        source_sha256=hashlib.sha256(source[start:end].encode()).hexdigest()))
regions.sort(key=lambda r: r['start'])
for a, b in zip(regions, regions[1:]):
    assert a['end'] <= b['start']
sealed = source
for index, region in reversed(list(enumerate(regions))):
    begin = ('section LoopBankSeal' + str(index) + '\n'
             + 'attribute [local irreducible] ' + ' '.join(definitions) + '\n'
             + 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n')
    end = ('end LoopBankSeal' + str(index) + '\n'
           + 'attribute [simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n\n')
    sealed = sealed[:region['start']] + begin + sealed[region['start']:region['end']] + end + sealed[region['end']:]
    instrumentation.extend([begin, end])
restored = sealed
for text in instrumentation:
    assert restored.count(text) == 1
    restored = restored.replace(text, '', 1)
assert restored == source
axioms = '\n' + '\n'.join('#print axioms Turing.FinTM.' + name for name in names) + '\n'
axioms += (OUT / 'metadata-appendix-v3.lean.txt').read_text()
(OUT / 'Loop-sealed-v4.lean.txt').write_text(sealed + axioms)
coverage = dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                sealed_input_sha256=hashlib.sha256((sealed + axioms).encode()).hexdigest(),
                sealed_definitions=definitions,
                default_simp_removed=['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg'],
                regions=regions, guard_before_docstring_and_header=True,
                instrumentation=instrumentation, appendix=axioms,
                removing_instrumentation_and_appendix_restores_source_bytes=True,
                unchanged_legacy_helpers_outside_guards=True,
                unrelated_matcher_not_claimed_sealed='Turing.FinTM.rewind_scan.match_1')
(OUT / 'seal-coverage-v4.json').write_text(json.dumps(coverage, indent=2) + '\n')
(OUT / 'control-definitions.txt').write_text('\n'.join(definitions) + '\n')
print(json.dumps(dict(regions=names, definitions=len(definitions),
                     source_restored=restored == source), indent=2))
