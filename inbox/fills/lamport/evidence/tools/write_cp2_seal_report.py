"""Write the checkpoint-2 report insertion from immutable raw seal/census results."""
import hashlib
import json
from pathlib import Path

base = Path('/private/tmp/tcslib-lamport-01a1d88f')
e = base / 'delivery/lamport/evidence'

def records(directory):
    return [json.loads(line) for line in (e / 'logs/seals' / directory / 'results.jsonl').read_text().splitlines()]

def mode(rows, letter):
    return next(row for row in rows if row.get('mode') == letter)

def errors(row):
    return [d for d in row['diagnostics'] if d['severity'] == 'error']

def names(row):
    return sorted({d['declaration'] for d in errors(row) if d.get('declaration')})

def bullets(values):
    return '\n'.join('- `' + value + '`' for value in values)

old = records('base-r1')
candidate = records('cp2-rule10-r1-Main-r1')
revised = records('cp2-rule10-r2-Main-r1')
base_a, base_b = mode(old, 'A'), mode(old, 'B')
first_a, first_b = mode(candidate, 'A'), mode(candidate, 'B')
new_a, new_b = mode(revised, 'A'), mode(revised, 'B')
assert len(errors(base_a)) == 0 and len(errors(base_b)) == 15 and len(names(base_b)) == 11
assert len(errors(first_a)) == 3 and len(errors(first_b)) == 25
assert names(first_b) == names(new_b)
assert new_a['status'] == 'SOURCE_PASS' and len(errors(new_b)) == 22 and len(names(new_b)) == 16
controls = [row for row in revised if row.get('expected_errors') is not None]
assert len(controls) == 6 and all(row['status'] == 'CONTROL_PASS' for row in controls)
assert all(row['errors'] == (1 if row['label'].endswith('Negative') else 0) for row in controls)
completion = json.loads((e / 'logs/base-auth/base-auth-cp2-completion.json').read_text())
assert completion['overall_complete'] and len(completion['effective_results']) == 8
inventory = e / 'logs/helper-checks/Inventory-cp2-rule10-r2-Main-inventory1.log'
axioms = []
for line in inventory.read_text().splitlines():
    if line.startswith('LAMP-AXIOMS\t'):
        f = line.split('\t')
        axioms.append(dict(constant=f[2], axioms=[v.strip() for v in f[3].strip('[]').split(',') if v.strip()]))
assert len(axioms) == 91
standard = {'propext','Classical.choice','Quot.sound'}
assert all(set(row['axioms']) <= standard | {'sorryAx'} for row in axioms)
assert [row['constant'] for row in axioms if 'sorryAx' in row['axioms']] == [
    'TCSlib.Cryptography.Authentication.lamport_oneTimeSecure']
review = e / 'seals/Cp2R2Main/explicit-unfold-review.json'
assert review.exists()
extra = sorted(set(names(new_b)) - set(names(base_b)))
text = f'''### Rule 10, controls and axioms at checkpoint 2

Mode A excludes `Complexity.PolyExpr.eval` as notation; mode B seals it too.
All results below are actual whole-file probes over the complete recorded TCSlib import
closure. No failed B run is replaced by an unsealed check or omitted from the payload.

**Pinned base, owned Lamport module.** At `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`,
A passed with zero errors and 1,445 requested definitions. B had 15 diagnostics in these
11 declarations, with 1,446 requested definitions:

{bullets(names(base_b))}

The first B obstruction is the unchanged definition-level equality between
`PolyExpr.var.eval n` and `n` in `lamportOWF`/`lamport`; later dependent declarations
cascade from it. All six original base controls passed. Each sealed negative failed
exactly once at its designated line. Raw requests, complete INSTALL/EOF coverage and
every diagnostic are in `evidence/logs/seals/base-r1/`.

**Pinned base, authorized Authentication facade.** Its base snapshot has zero local
stored constants and exactly 149 canonical TCSlib dependency modules. Both A and B pass,
with 1,944 and 1,945 requested definitions respectively; all six paired controls pass,
and each negative fails exactly once. This base environment was obtained by checking
canonical pinned-base Lamport and HashAndSign in this worker's existing olean tree.
All 147 other provider oleans were unchanged. The census rejects unexpected TCSlib module
homes, so final helper imports cannot silently enter this baseline.

The first facade queue completed both source seals and five controls; its B-reader
control was interrupted by the host cap before INSTALL/EOF. The filtered retry reused
the identical request record only after checking that both freshly built canonical base
oleans were byte-identical to the census environment and all 147 provider hashes matched.
The B-reader finally passed in `baseauth-cp2-r2-seals-host5`. Failed host attempts remain
in the payload. The exact final source bytes were restored and final Lamport,
HashAndSign and Authentication were rechecked successfully. The rollup and all original
results are retained under `evidence/logs/base-auth/base-auth-cp2-completion.json`,
`evidence/logs/base-auth/baseauth-cp2-r1/`, `evidence/logs/base-auth/baseauth-cp2-r2/`
and `evidence/logs/seals/baseauth-cp2-*/`. No olean tree was copied or joined.

**First checkpoint-2 candidate, `11cc4e54fb63bb1c6310e90e6fbaa07e7031fb07`.** A produced
three command diagnostics at source line 765: the unconditional local attributes tried
to mark `ProbComp.expect`, `ProbComp.sample` and `OracleComp.bind` irreducible when the
seal had already done so. The source mapper attaches them to the preceding
`TCSlib.Cryptography.Authentication.lamport_forgerCodec` declaration; they are attribute
installation errors, not three failures of that theorem's proof. B produced 25 errors.
All six controls passed. All raw results and failing sources are preserved in
`evidence/logs/seals/cp2-rule10-r1-Main-r1/`.

**Revised candidate, `77ec7bb1255852eb6288c6c38577a540a5e1a266`.** The native source fix makes
the same local attribute installation idempotent in main, Statistics and Experiment,
without unsafe reducibility, unsealing, a new public metaprogram API, or a statement change.
Statistics, Experiment, Lamport, HashAndSign and Authentication all pass their fresh
native checks. Revised main A passes with zero errors; B has 22 errors. Both candidates'
B errors map to the same following 16 declarations, all listed here:

{bullets(names(new_b))}

This is the inherited 11-declaration list plus:

{bullets(extra)}

The additional B diagnostics are retained as dependent application/type cascades after
the unchanged constructor-level B obstruction; they are not claimed to pass. For example,
the codec diagnostic reports `f` being supplied to the errored `lamport` application
where the remaining elaborated argument expects `List Bool → List Bool`. The repaired
local installation command contributes no new A or B error.

Revised main A/B INSTALL and EOF coverage validate all 1,492/1,493 requested definitions.
All six revised controls pass: both unsealed and reader controls compile, and each sealed
negative has exactly one error at its designated line. The full lists, line mappings,
source snapshots and raw diagnostics are in `evidence/logs/seals/cp2-rule10-r2-Main-r1/`.

**Stored constants and explicit scan.** The revised main census prints the axioms of all
91 stored constants. Ninety use only subsets of `propext`, `Classical.choice` and
`Quot.sound`. The still-admitted `lamport_oneTimeSecure` alone additionally uses `sorryAx`;
its exact set is `[Classical.choice, Quot.sound, propext, sorryAx]`. No other nonstandard
axiom occurs. This is checkpoint evidence, not a claim that the target is proved.
The complete census is in `evidence/logs/helper-checks/Inventory-cp2-rule10-r2-Main-inventory1.log`.

The explicit-unfold scan recorded 376 token readings and 15 review candidates. All 15
are benign: 12 are local-name/parameter-label suffix matches; two are arguments to
published reader lemmas; one is an unchanged outer function in a representation equality.
There is no forbidden explicit foreign unfold. The raw scan and row-by-row review,
bound to the revised source and inventory hashes, are
`evidence/seals/Cp2R2Main/explicit-unfold-scan.json` and
`evidence/seals/Cp2R2Main/explicit-unfold-review.json`.

**Remaining final-delivery checks.** Whole-file final seals for the helpers and final
Authentication facade are still pending. When the target proof and final machine imports
land, main must be sealed again too. This intermediate checkpoint does not claim those
omitted final checks complete.
'''
out = base / 'drafts/Cp2SealReportBlock.md'
assert not out.exists()
out.write_text(text)
print(out)
print('Verified report inputs: base A0/B15, first A3/B25, revised A0/B22,91 own constants,6 valid controls.')
