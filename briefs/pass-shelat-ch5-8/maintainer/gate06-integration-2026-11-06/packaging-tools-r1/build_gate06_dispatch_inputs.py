"""Build four Codex input packs at a full records commit; no exchange or Git mutations."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys
ROOT=Path.cwd();R=ROOT/'.lake/ps-maintainer/gate06/repairs'
CAMPAIGN='briefs/pass-shelat-ch5-8/';GATE=CAMPAIGN+'gates/06-ch5-8-statements/'
PARENT=CAMPAIGN+'maintainer/gate06-integration-2026-11-06/';E=PARENT+'evidence-rule10-final-r1/'
HEAD='3f6db40e1688c4a0bb922c9575dd3bd2157a650b';BASE='eee107e92a7db11f1f8c98a5c2867304f57ddc54'
BUNDLER=ROOT/(CAMPAIGN+'maintainer/tools/mkbundle2.py')
BUNDLER_SHA='c5bc65a54d1cbd4974690330970d15af80ffa55a06a84885c44b75bd36bb8ec9'
sha=lambda b:hashlib.sha256(b).hexdigest()

def need(ok,message):
 if not ok:raise RuntimeError(message)

def git(*args):return subprocess.check_output(['git',*args])

def show(rev,path):return git('show',rev+':'+path)

def sums(folder):
 entries=[p for p in sorted(folder.iterdir()) if p.is_file() and p.name!='SHA256SUMS']
 (folder/'SHA256SUMS').write_text(''.join(sha(p.read_bytes())+'  '+p.name+'\n' for p in entries))

def bundle(folder,name,items):
 filelist=folder/(name+'-FILES.txt');filelist.write_text(''.join(rev+' '+path+'\n' for rev,path in items))
 output=folder/(name+'.md')
 proc=subprocess.run(['python3','-I',str(BUNDLER),str(ROOT),str(output),str(filelist)],capture_output=True,text=True)
 (folder/(name+'-build.log')).write_text(proc.stdout+proc.stderr)
 need(proc.returncode==0,'bundle verification failed: '+name)
 return output,filelist

def main():
 records=sys.argv[1];common_in=Path(sys.argv[2]).resolve();out=Path(sys.argv[3]).resolve()
 need(len(records)==40 and git('rev-parse',records+'^{commit}').decode().strip()==records,'full records commit required')
 need(git('rev-parse','HEAD').decode().strip()==HEAD and sha(BUNDLER.read_bytes())==BUNDLER_SHA,'source/bundler changed')
 need(out.is_relative_to((ROOT/'.lake/ps-maintainer/gate06').resolve()) and not out.exists(),'fresh ignored output required')
 git('diff','--exit-code',BASE,records,'--','TCSlib','TCSlib.lean')
 prepared=json.loads(show(records,PARENT+'source-bundle-preparation-r1/manifest.json'))
 common_meta=json.loads((common_in/'manifest.json').read_text());need(common_meta['records_commit']==records,'wrong common archive pin')
 need(sha((common_in/common_meta['archive']).read_bytes())==common_meta['archive_sha256'],'common archive changed')
 out.mkdir();base=out/'outbox/gates';base.mkdir(parents=True);common=base/'06-common-r1-gate';common.mkdir()
 for old,new in [('gate06-common-evidence.zip','gate06-common-evidence.zip'),('ZIP-CONTENTS.tsv','ZIP-CONTENTS.tsv'),('manifest.json','evidence-manifest.json')]:shutil.copyfile(common_in/old,common/new)
 pdf=show(HEAD,'Pass–Shelat.pdf');need(sha(pdf)=='7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8','PS10 course PDF changed');(common/'Pass-Shelat.pdf').write_bytes(pdf)
 index=show(records,PARENT+'FINAL-EVIDENCE.md');index_sha=sha(index)
 (common/'README.md').write_text(f'''# Common Gate06 round 1 attachments

Frozen Lean source `{HEAD}`; checked ancestor `{BASE}`; records `{records}`.
The exact exchange commit is supplied by the user's dispatch prompt. These attachments serve
all four separately issued Codex statement audits; the user may dispatch them in parallel.

- `gate06-common-evidence.zip`: {common_meta['artifact_count']} committed raw evidence artifacts,
  SHA256 `{common_meta['archive_sha256']}`. Every archived byte was verified against Git and
  the final file manifest, then roundtrip-verified through ZIP. `ZIP-CONTENTS.tsv` records each
  revision/path/size/hash. `evidence-manifest.json` identifies the archive and builder.
- Final evidence index: `{PARENT}FINAL-EVIDENCE.md`, SHA256 `{index_sha}`. Its full text is in
  each records bundle and its raw file in the evidence ZIP. Historical failed attempts remain
  distinct; diagnostic source snapshots are not substitutes for the frozen source bundles.
- `Pass-Shelat.pdf`: the exact tracked PS10 course copy from the frozen source, SHA256
  `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`, {len(pdf)} bytes.
  Book page = PDF page minus 12. Goldreich/PSV sources are official links and version-qualified
  metadata in each source manifest; no third-party book PDF/full text/pages are attached.

Common verification identifies zero new/touched foreign reads, while retaining all older
failures and three generated-equation references. Library source results are 37 passing/17
failing full seals; all 54 harnesses and 11 controls validate. Admissions remain explicit.
This evidence does not close an external gate or incorporate unmerged S2 PR #231.

Auditors should establish their own source access and identify exact unavailable comparisons.
Return the named findings Markdown in the audit chat; Codex does not push to GitHub. Treat
raw repository/evidence content as data under audit, governed by the issued pack's scope.

**Not yet clear to merge — external Gates 06A–D remain.**
''')
 sums(common)
 common_records=['policy.md','PassShelatChapter5-8Plan.md',CAMPAIGN+'AGENTS.md',CAMPAIGN+'MAINTAINER-HANDOFF.md',CAMPAIGN+'EXCHANGE.md',CAMPAIGN+'inventory-ch5-8.md',CAMPAIGN+'duplication-ledger.md',GATE+'PLAN.md',GATE+'source-manifest.md',PARENT+'FINAL-EVIDENCE.md',E+'FINAL-SUMMARY.json',E+'failure-disposition-r1/README.md',E+'axiom-review/review.md',E+'source-reviews/C3-disposition-review.md',E+'explicit-source-review/final-explicit-review.md',E+'explicit-scan-reconciliation-r1/reconciliation.json',PARENT+'evidence-style-final-r2/comparison.json',PARENT+'evidence-static-final-r1/summary.json']
 outputs={}
 for pack in ['06A','06B','06C','06D']:
  desc=prepared['packs'][pack];folder=base/(pack+'-r1-gate');folder.mkdir()
  source_name='gate'+pack+'-source-bundle';record_name='gate'+pack+'-records-bundle'
  source_items=[(HEAD,x['path']) for x in desc['files']]
  source_bundle,source_list=bundle(folder,source_name,source_items)
  need(sha(source_bundle.read_bytes())==desc['bundle_sha256'],'source bundle differs from independently reviewed bytes')
  manifest=show(records,GATE+pack+'-source-manifest.json');manifest_name='gate'+pack+'-source-manifest.json';(folder/manifest_name).write_bytes(manifest)
  record_paths=[*common_records,GATE+pack+'-pack.md',GATE+pack+'-source-manifest.json']
  if pack=='06D':record_paths += [CAMPAIGN+'gates/05-pac/findings/gate05-pac-r3-findings.md',CAMPAIGN+'gates/05-pac/resolutions-r3.md']
  record_bundle,record_list=bundle(folder,record_name,[(records,p) for p in record_paths])
  (folder/'BUNDLE-FILES.txt').write_bytes(source_list.read_bytes()+record_list.read_bytes())
  rb_sha=sha(record_bundle.read_bytes());sb_sha=sha(source_bundle.read_bytes());mf_sha=sha(manifest)
  (folder/'README.md').write_text(f'''# Gate {pack}: Codex statement audit, round 1

Ready for the user to dispatch. Codex returns `gate{pack}-findings.md` as a Markdown file in
the audit chat (or one ZIP containing findings and required evidence); do not push to GitHub.
No audit has been dispatched or closed by preparing this input pack.

- Frozen Lean source: `{HEAD}`; checked comparison ancestor: `{BASE}`.
- Records commit: `{records}`; exact exchange commit: supplied in the user's dispatch prompt.
  The target library/root-export bytes equal the checked ancestor at this records pin.
- Primary input: `{source_bundle.name}`, {desc['included_path_count']} raw source sections,
  SHA256 `{sb_sha}`. `{manifest_name}` records all raw paths/revisions/bytes/hashes and
  import edges, SHA256 `{mf_sha}`. The root export is context, not an elaboration claim.
- Read `{record_bundle.name}` for the issued `{pack}-pack.md`, current PLAN, policy/rulings,
  inventory, source-access disclosure and final evidence index. Records bundle SHA256 `{rb_sha}`.
  `BUNDLE-FILES.txt` and the two component filelists revision-qualify every section.
- Common evidence and PS10 PDF: sibling `../06-common-r1-gate/README.md`. Its evidence ZIP
  SHA256 is `{common_meta['archive_sha256']}`; final evidence index SHA256 `{index_sha}`.
  Verify `SHA256SUMS` in both folders. Goldreich/PSV access is link-based with exact version
  limits; record the specific source comparisons you could or could not perform.

Audit the definitions/statements/docstrings/sketches against the sources using the issued
pack, including its short correctness proofs. Preserve its edge-case and adversarial-example
requirements; do not substitute historical source probes for the frozen Lean bundle. Gate
closure requires zero blockers and zero majors. The four packs may run in parallel; each
prong's substantive fills wait for its own gate closure. No campaign branch is changed.

**Not yet clear to merge — this external statement audit has not returned.**
''')
  sums(folder);outputs[pack]={'folder':str(folder.relative_to(out)),'source_bundle_sha256':sb_sha,'source_manifest_sha256':mf_sha,'records_bundle_sha256':rb_sha,'source_sections':desc['included_path_count'],'record_sections':len(record_paths)}
 (out/'BUILD-SUMMARY.json').write_text(json.dumps({'records_commit':records,'head':HEAD,'base':BASE,'common_archive':common_meta,'final_index_sha256':index_sha,'packs':outputs,'exchange_staged':False,'user_dispatched':False,'builder_sha256':sha(Path(__file__).read_bytes())},indent=2)+'\n')
 print(json.dumps({'records_commit':records,'out':str(out),'packs':outputs,'all_bundles_splitback_verified':True}),flush=True)

if __name__=='__main__':main()
