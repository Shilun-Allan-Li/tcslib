"""Retain exact unchanged-block witnesses; do not alter historical cleanup rows."""
from pathlib import Path
import csv
import hashlib
import json
import re
import subprocess

root = Path.cwd()
records = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
campaign = records / 'briefs/pass-shelat-ch5-8'
e = campaign / 'maintainer/gate06-integration-2026-11-06/evidence-rule10-r2'
pins = json.loads((e / 'pins.json').read_text())
review = root / '.lake/ps-maintainer/gate06/repairs/base-failure-classification.md'
source = review.read_text()
files = {'Loops':'TCSlib/Complexity/ClassP/BinaryArith/Loops.lean',
         'Adversary':'TCSlib/Cryptography/Asymptotic/Adversary.lean',
         'BlockEncryptor':'TCSlib/Cryptography/Asymptotic/BlockEncryptor.lean'}
old_inventory = campaign / 'gates/07-eqlemmas/evidence-r2/r6c/cleanup-b-decls.tsv'
old_rows = [line.split('\t') for line in old_inventory.read_text().splitlines()]
matches = re.findall(r'^\| `(Loops|Adversary|BlockEncryptor)` \| `([^`]+)` \| (\d+)–(\d+) \| (\d+)–(\d+) \| `([0-9a-f]{64})` \| (\*\*Absent\*\*|\d+) \|$',source,re.M)
assert len(matches) == 15
rows=[]
for module,name,a,b,c,d,digest,historical in matches:
    path=files[module]
    get=lambda rev: subprocess.check_output(['git','show',rev+':'+path]).splitlines(keepends=True)
    before=b''.join(get(pins['base'])[int(a)-1:int(b)])
    after=b''.join(get(pins['head'])[int(c)-1:int(d)])
    assert before == after and hashlib.sha256(before).hexdigest() == digest
    hits=[i for i,row in enumerate(old_rows,1) if row == [path,name]]
    if historical == '**Absent**':
        assert not hits
    else:
        assert hits == [int(historical)]
    rows.append({'file':path,'source_declaration':name,'base_start':a,'base_end':b,'head_start':c,'head_end':d,
                 'unchanged_raw_block_sha256':digest,'historical_declaration_row':';'.join(map(str,hits)),
                 'classification':'UNTOUCHED_INHERITED; NOT_REPAIRED',
                 'base':pins['base'],'observed_head':pins['head'],
                 'observation':'HEAD combined import-closure seal failed; no native base seal rerun claimed'})
assert sum(not row['historical_declaration_row'] for row in rows) == 10
dest=e/'inherited-observations'
assert not dest.exists()
dest.mkdir()
(dest/'source-review.md').write_bytes(review.read_bytes())
(dest/'record_inherited_reads.py').write_bytes(Path(__file__).read_bytes())
with (dest/'observations.tsv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t',lineterminator='\n')
    writer.writeheader();writer.writerows(rows)
(dest/'summary.json').write_text(json.dumps({'declarations':15,'head_diagnostics':16,
    'linked_historical_declarations':5,'newly_observed_inherited_declarations':10,
    'historical_inventory_modified':False,'base_seal_rerun':False,
    'source_review_sha256':hashlib.sha256(review.read_bytes()).hexdigest(),
    'limit':'Reconciliation input only. No failing module or proof is declared passing.'},indent=2)+'\n')
brief=campaign/'fills/cleanup-part2/brief-draft.md'
old='  and the base reads the fill reviews named: `primesPairEquiv_apply_val`, `exists_fullLengthExcept`,\n'
new=('  plus the fifteen unchanged-declaration observations from Gate 06\n'
     '  (`maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/inherited-observations/`):\n'
     '  five link to the historical inventory; ten `BinaryArith/Loops` declarations are newly\n'
     '  observed inherited debt. Deduplicate these at the post-S2 issue base; do not add ten\n'
     '  blindly to the historical 764-row count or treat inventory additions as repairs;\n'
     '  and the base reads the fill reviews named: `primesPairEquiv_apply_val`, `exists_fullLengthExcept`,\n')
s=brief.read_text();assert s.count(old)==1;brief.write_text(s.replace(old,new))
print(json.dumps({'declarations_verified_byte_identical':len(rows),'historical_links':5,'new_inherited_observations':10}))
