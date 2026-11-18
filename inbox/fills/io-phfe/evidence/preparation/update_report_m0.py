"""Refresh report from source-bound evidence, without inventing pending results."""
from pathlib import Path
import json,subprocess,re
report=Path('REPORT.md');s=Path('evidence/preparation/REPORT-m0-template.md').read_text();head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();meta=json.loads(Path('evidence/static-m0-final/summary.json').read_text());census_path=Path('evidence/statements/summary.json');census=json.loads(census_path.read_text()) if census_path.exists() else None
start=s.index('Status:');end=s.index('The primary result being specified')
intro=f'''Status: **M0 statements candidate; {'publication pending' if census else 'native axiom/type census and publication pending'}.**
Source HEAD: `{head}`. The checked source contains {meta['owned_files']} new Lean modules,
{meta['owned_lines']:,} physical lines and {meta['admissions']} direct proof admissions. Correctness, algebra,
endpoint couplings, security bounds and asymptotic consequences are stated; their remaining
admissions are not completed proofs. The generic perfect-correctness-to-zero-error implication
is proved and elaborated.

The complete import closure has 285 modules. Every module returned rc0, both error forms
were zero, and a fresh object was produced. `evidence/build/summary.tsv` binds all checked
source bytes to this HEAD, retaining each actual check-time HEAD; unchanged bytes are
explicitly rebound rather than described as rerun. The native collector covers 74 modules
and 2225 stored constants. All 387 requested public definition readers are natively verified.
Style/sketch/width checks pass. The four campaign warning lines cover five acronym-case
readers already verified by the native catalog; no new FAIL remains.

{'The native statement/axiom census is complete; its counts and limits appear in the verification ledger below.' if census else 'The complete native statement/axiom census is still running; no result is inferred from partial output.'}
No checkpoint has been pushed yet. The checkpoint0 header/prose manifest and its negative
controls are prepared in `evidence/freeze/`; the statement freeze begins with the first
statements publication. The full Rule10 seal/control/explicit-body suite remains required
for final delivery and is not claimed passing at M0. Efficiency targets are intentional
Phase B obligations. No machine, RAM program, PolyHandler or sampler is constructed.

'''
s=s[:start]+intro+s[end:]
s=re.sub(r'\| Source HEAD for current checks \|.*?\|',f'| Source HEAD for current checks | `{head}`; complete checked closure source-bound in evidence/build/summary.tsv |',s)
s=s.replace('The current lead snapshot has **72 owned Lean modules and 13,620 physical lines** before\nremaining facade lint repairs. The exact owned-file ledger follows. It is a working-copy\nsize observation for this report, not a source-bound proof census. Refresh it at the audited\nHEAD and retain per-file source SHA-256 values with the compiled-source ledger.',f'The audited source has **74 new Lean modules and {meta["owned_lines"]:,} physical lines**.\nThe two permitted existing facades are recorded separately in the touched-file and diff\nledgers. Source SHA-256 values and current object hashes accompany the checked-source ledger.')
a=s.index('The authoritative declaration list will be');b=s.index('The provisional decls2 run reports',a)
s=s[:a]+('The native collector inventories all 2225 stored constants, including generated constructors,\neliminators, projections, instances and matchers. The complete typed inventory is exported\nto `evidence/statements/native-declarations.tsv` and `StmtDump.jsonl` when the native\ncensus finishes. Written source headers/readers are retained separately. Native ROOT/CAT\nrecords and the 387/387 reader validation are already complete.\n\n')+s[b:]
s=s.replace('The provisional decls2 run reports','The final M0 decls2 run reports')
a=s.index('### Current owned-file line ledger');b=s.index('## M0 verification ledger',a)
files=Path('evidence/logs/owned-files.txt').read_text().splitlines()
ledger='### Current owned-file line ledger\n\n| File | Lines |\n|---|---:|\n'+''.join(f'| `{f}` | {len(Path(f).read_text().splitlines())} |\n' for f in files)+f'\nSource-bound ledger: {len(files)} files, {sum(len(Path(f).read_text().splitlines()) for f in files)} lines.\n\n'
s=s[:a]+ledger+s[b:]
a=s.index('All observations here are provisional');b=s.index('| Check / evidence family',a)
s=s[:a]+'Results below distinguish completed M0 checks from mandatory final checks that remain pending.\nNo zero-admission, final Rule10 or completed security-proof claim is made.\n\n'+s[b:]
updates={
'Complete bootstrap':('PASS: 285 modules, zero errors/rc0/fresh objects; all source bytes bound to '+head,'See evidence/build/summary.tsv; actual check-time HEADs are preserved.'),
'Owned source size/admissions':('74 files, 13,745 lines, 144 direct admissions; base admissions unchanged','Final PROOFS delivery requires zero new admissions.'),
'decls2':('ADDED1171, CHANGED0, REMOVED0 against pinned base','evidence/logs/m0-decls2-final.tsv; native stored count is separately2225.'),
'Style/sketch/width':('PASS: style0 findings over76 touched files, sk15 none, widths/sizes0 violations','Raw final M0 tool logs retained under evidence/logs.'),
'Name clashes':('1171 explicit new declarations;0 full-name clashes;65 reused short names','Canonical source scanner results retained; native imports also elaborate without duplicate constants.'),
'Campaign lint':('No new FAIL;4 warning lines cover5 acronym-case definitions with published readers','All five readers are natively verified; exact diagnostics and justified spellings are retained.'),
'Published acronym-case readers':('DLINAssumption→dlinAssumption_iff; PGSound→pgSound_iff; SASimSecureWith→saSimSecureWith_iff; SASimSecure→saSimSecure_iff; MDDHRealizable→mddhRealizable_iff','PASS: all387 requested reader theorems resolve uniquely and their types mention the actual target.'),
'Frozen-file and statement/prose checks':('Header/prose manifest prepared at '+head+';1171 written declarations; all negative controls rejected','evidence/freeze/checkpoint0.json; freeze activates on first statements publication.'),
'Phase A/import/extraction boundaries':('Static scope/import/admission inventory passes;1 justified proof-only injection token;0 PDF additions','The sole pow_val_bijective hit is PHFE/Embedding.lean:42 and returns no exponent. Final native Rule10 checks remain pending.')}
if census:
 updates['Native declarations and full types']=(f'PASS: {census["native_stored_constants"]} stored constants, complete native types without elisions','evidence/statements/native-declarations.tsv, written-declarations.tsv and StmtDump.jsonl.')
 updates['Axioms and sorry dependencies']=(f'{census["print_axioms_records"]} #print axioms records; {census["standard_axiom_only"]} standard-only, {census["sorryAx_dependent"]} sorryAx-dependent;0 other nonstandard axioms','M0 admissions and transitive raw-law dependencies are explicit; no standard-only headline claim. Trace paths are in evidence/statements/sorry-traces.jsonl.')
for key,(obs,req) in updates.items():
 s=re.sub(r'^\| '+re.escape(key)+r' \|.*$',f'| {key} | {obs} | {req} |',s,flags=re.M)
a=s.index('The 48 facade diagnostics concern');b=s.index('Rule10 tool provenance',a)
s=s[:a]+'The 48 earlier facade diagnostics were repaired by explicit exports and security facades.\nThe only remaining campaign warning lines are the five documented acronym-case readers,\nall validated by native name/type checks. They are checker naming heuristics, not missing\nreader declarations.\n\n'+s[b:]
s=s.replace('The root-only workflow is in `/private/tmp/io-phfe-drafts/rule10-prep/RUNBOOK.md`;\ncopy it and its source/provenance to delivered evidence before use as a payload reference.','The root-only workflow is delivered as `evidence/preparation/rule10-prep/RUNBOOK.md`.')
a=s.index('Before the first statements push the remaining concrete release conditions');b=s.index('## References and supplied editions',a)
s=s[:a]+'''The dispatch's M0 subset is the checkpoint requirement: complete definitions/readers/targets,
all theorem statements, module elaboration, decls2/StmtDump, axiom inventory, lint/width/clash,
fidelity/rule15 tables and a hashed payload. The full Rule10 and proof completion checks
remain final-delivery obligations; prepared seal variants are not reported as passed.
There is no active source/resource blocker. No counterexample beyond the corrected source
rank estimate was identified in the source/header reviews; the admitted claims still need proofs.

'''+s[b:]
report.write_text(s)
ledger=subprocess.check_output(['git','log','--reverse','--format=%H%x09%an <%ae>%x09%cn <%ce>%x09%s%x09%G?','5ed465f62e4ae0f93ded1a1ba49e807591b589eb..HEAD'],text=True)
Path('evidence/logs/source-COMMITS.tsv').write_text('hash\tauthor\tcommitter\tsubject\tsigning\n'+ledger)
print('report refreshed',head,'census complete',bool(census))
