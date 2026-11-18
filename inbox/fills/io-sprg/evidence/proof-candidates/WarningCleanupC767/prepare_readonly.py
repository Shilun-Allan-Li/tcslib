"""Temp-only warning triage/diffs. Does not apply edits or invoke any compiler/tool."""
from pathlib import Path
import csv
import difflib
import hashlib
import io
import json
import re

W=Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
B=Path('/private/tmp/io-sprg-proof-notes/WarningCleanupC767')
AREA='TCSlib/Cryptography/Obfuscation/StructuredSeed/'
HEAD='c767ee867e76c0b1248cee46d4af5296ffa078d5'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
base={r['file']:r for r in json.loads((W/'evidence/checks/m3-final/sizes-widths.json').read_text())['files']}
edits=[
 {'id':'W01','file':'LPN.lean','theorem':'lpnNoise_law','lines':[107],
  'before':'      by_cases ha : c.1 = 0 <;> simp [ha, hz, Ne.symm hz]',
  'after':'      by_cases ha : c.1 = 0 <;> simp [ha, Ne.symm hz]',
  'reason':'Linter specifically marks hz unused when Ne.symm hz is already supplied; remove only that argument.'},
 {'id':'W02','file':'Degree.lean','theorem':'Internal.weightedTotalDegree_X_le','lines':[136],
  'before':'    Finset.sup_le fun d hd =>','after':'    Finset.sup_le fun _d hd =>',
  'reason':'Unused lambda binder is proof-local. Leading underscore retains exactly the same lambda type and avoids a theorem-header edit.'},
 {'id':'W03','file':'Correctness.lean','theorem':'Params.G4_eval_sdCore','lines':[399],
  'before':'  | none => simp [hf]','after':'  | none => simp',
  'reason':'The cases substitution already specializes first to none; hf is an unused simp argument. Keep the outer named cases equation because the some branch uses it.'},
 {'id':'W04','file':'Correctness.lean','theorem':"Params.eval'_correct",'lines':[441,441],
  'before':"  cases he : x.err <;>\n    cases hb : P.G.eval (P.n κ) I.1 x.σ (P.outputIndex κ j) <;> simp [he, hb]",
  'after':"  cases x.err <;>\n    cases P.G.eval (P.n κ) I.1 x.σ (P.outputIndex κ j) <;> simp",
  'reason':'Both case equalities are unused in simp after the cases reductions. Remove the unused simp arguments and their unneeded equation labels.'},
 {'id':'W05','file':'Correctness.lean','theorem':'Params.G4_seed_allOutputs','lines':[471],
  'before':'      cases he : x.err <;> simp [he]','after':'      cases x.err <;> simp',
  'reason':'The pure-branch Boolean cases reduction already determines the expressions; remove unused equation label/simp argument.'},
 {'id':'W06','file':'Stretch.lean','theorem':'Params.seedBitsAt_le','lines':[192,192],
  'before':'  convert hbits using 1 <;> dsimp only [K, X, a] <;> ring',
  'after':'  convert hbits using 1\n  dsimp only [K, X, a]\n  ring',
  'reason':'Both unnecessarySeqFocus diagnostics say the following tactic sees only one goal. Use ordinary consecutive tactics, retaining convert/dsimp/ring.'},
 {'id':'W07','file':'Stretch.lean','theorem':'Internal.eventually_seed_relative_gap','lines':[298,298],
  'before':"    field_simp [(Real.rpow_pos_of_pos hxpos b).ne'] <;> ring",
  'after':"    field_simp [(Real.rpow_pos_of_pos hxpos b).ne']",
  'reason':'field_simp already closes this equality. The subsequent ring is both unreachable and unused; delete only that suffix.'},
 {'id':'W08','file':'Stretch.lean','theorem':'jls_hasPolyStretch','lines':[463,463],
  'before':"    field_simp [hN.ne'] <;> ring",'after':"    field_simp [hN.ne']",
  'reason':'field_simp already closes the eta identity; remove unreachable/no-op ring.'}
]
bindings=[]
for name in ['LPN.lean','Degree.lean','Correctness.lean','Stretch.lean']:
    rel=AREA+name;path=W/rel;raw=path.read_bytes()
    assert sha(path)==base[rel]['sha256'],'Source no longer c767; use preserved bytes/hunk review'
    (B/'base-source'/(name+'.txt')).write_bytes(raw)
    before=raw.decode();after=before
    for edit in [r for r in edits if r['file']==name]:
        assert after.count(edit['before'])==1,(name,edit['id'])
        after=after.replace(edit['before'],edit['after'],1)
    # No new proof block/declaration/comment is introduced. Every replacement is
    # inside an existing body (the one term-proof lambda is after its :=).
    assert len(re.findall(r':=\s*by\b',before))==len(re.findall(r':=\s*by\b',after))
    assert re.findall(r'/--.*?-/',before,re.S)==re.findall(r'/--.*?-/',after,re.S)
    assert re.findall(r'^(?:theorem|lemma|def|structure|namespace|end)\b.*$',before,re.M)==re.findall(r'^(?:theorem|lemma|def|structure|namespace|end)\b.*$',after,re.M)
    diff=''.join(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),fromfile='a/'+rel,tofile='b/'+rel,n=3))
    (B/(name+'.proof-only.diff')).write_text(diff)
    bindings.append({'file':rel,'base_source_head':HEAD,'base_sha256':sha(path),
      'proposed_sha256':hashlib.sha256(after.encode()).hexdigest(),
      'changed_headers':False,'changed_docstrings':False,'new_tactic_blocks':0,
      'edit_ids':[r['id'] for r in edits if r['file']==name],
      'status':'NOT_APPLIED_NOT_COMPILED; root must merge hunks against any newer source'})
triage=[]
for name in ['LPN.lean','Degree.lean','Correctness.lean','Stretch.lean']:
    log=W/'evidence/build/M3/all-owners/mods'/('TCSlib_Cryptography_Obfuscation_StructuredSeed_'+name[:-5]+'.log')
    lines=log.read_text().splitlines()
    for i,line in enumerate(lines):
        if 'warning:' not in line or 'sorry' in line:continue
        m=re.match(r'(.+\.lean):(\d+):(\d+): warning: (.*)',line);assert m
        matching=[r for r in edits if r['file']==name and int(m[2]) in r['lines']]
        assert len(matching)==1
        e=matching[0]
        triage.append({'file':m[1],'line':int(m[2]),'column':int(m[3]),'owner_theorem':e['theorem'],
         'warning':m[4],'unused_argument':lines[i+1].strip() if 'simp argument' in m[4] else '',
         'cleanup_id':e['id'],'reason':e['reason'],'source_log':str(log.relative_to(W)),
         'source_log_sha256':sha(log),'validation':'NOT_RUN'})
assert len(triage)==12 and len(edits)==8
out=io.StringIO();writer=csv.DictWriter(out,fieldnames=list(triage[0]),delimiter='\t',lineterminator='\n');writer.writeheader();writer.writerows(triage)
(B/'warning-triage.tsv').write_text(out.getvalue())
(B/'exact-replacements.json').write_text(json.dumps(edits,indent=2,ensure_ascii=False)+'\n')
(B/'source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
(B/'warning-triage.json').write_text(json.dumps({'source_head':HEAD,'warning_count':12,'proof_body_edits':8,
 'scope':'4 files, 8 body-only hunks; declarations/docs unchanged; no new tactic blocks',
 'status':'NOT_APPLIED_NOT_COMPILED','warnings':triage},indent=2,ensure_ascii=False)+'\n')
print('Prepared12 exact warning rows and8 proof-only candidate edits across4 files; NOT APPLIED/NOT RUN')
