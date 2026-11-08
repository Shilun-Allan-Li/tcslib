"""Root-reviewed one-shot final C3 launcher; no retry or clearance inference."""
from pathlib import Path
import hashlib, importlib.util, json, subprocess, sys
sys.dont_write_bytecode = True
ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
REPAIRS = ROOT / '.lake/ps-maintainer/gate06/repairs'
DRIVER = REPAIRS / 'run_gate06_final_native.py'
DRIVER_SHA = 'ea720bbe6fef9467efef1f8dbeb8c01ca3bb3b66e597a3ed2b3ce512f774f509'
ADAPTER_SHA = '04fadc8dc5f399a6d04e336b1a18f7859dc793e05124da9d6149771c2ba5890d'
FILES = {
 'final-c3-supplement-r2.source.txt':'26f74568c53a3552173e58c4267c7fcae7108ba562c121f1f2360f0f02c4c2bb',
 'final-c3-supplement-r2-manifest.json':'faa6852a84dd761f2b14dd6b178b9ef524a3876ec9e673e9f602359ced0b53f3',
 'final-c3-supplement-r2-notes.md':'8b94aec0d910e46cd06ba5965c8f9fa3b59a0150f335561b1cc7dc6a9d073a30',
}
sha = lambda raw: hashlib.sha256(raw).hexdigest()

def need(ok, message):
 if not ok:
  raise RuntimeError(message)

def main():
 need(Path.cwd() == ROOT, 'wrong cwd')
 need(sha(DRIVER.read_bytes()) == DRIVER_SHA, 'unreviewed driver')
 for name, digest in FILES.items():
  need(sha((REPAIRS/name).read_bytes()) == digest, 'proposal changed: ' + name)
 spec=importlib.util.spec_from_file_location('g06_c3_frozen_context',DRIVER)
 driver=importlib.util.module_from_spec(spec); spec.loader.exec_module(driver)
 ctx=driver.load_context(ADAPTER_SHA)
 for kind, count in [('seals',len(ctx.modules)),('controls',11)]:
  d=driver.read_json(driver.EVIDENCE / ('native-' + ('seal' if kind=='seals' else 'control') + '-runs') / 'summary.json')
  need(d['kind']==kind and d['head']==ctx.pins['head'] and d['base']==ctx.pins['base'], 'wrong preceding run')
  need(d['complete'] and d['completed_probes']==d['expected_probes']==count and d['all_harnesses_valid'] and not d['harness_failures'], 'preceding run incomplete/invalid')
  if kind=='controls':
   need(d['all_controls_verified'], 'preceding controls did not verify')
 manifest=json.loads((REPAIRS/'final-c3-supplement-r2-manifest.json').read_text())
 need(manifest['modules']==sorted(ctx.modules) and manifest['head']==ctx.pins['head'] and manifest['base']==ctx.pins['base'], 'C3 scope differs')
 scratch=ROOT/'.lake/ps-maintainer/gate06/rule10-final-c3-r2'
 need(not scratch.exists(), 'do not overwrite a native attempt')
 need(subprocess.run(['git','check-ignore','-q',str(scratch)],cwd=ROOT).returncode==0, 'scratch must be ignored')
 driver.assert_frozen(ctx)
 scratch.mkdir()
 source=Path(manifest['intended_probe_path'])
 need(source.parent==scratch and source.name=='G06C3SupplementR2.lean', 'unexpected C3 path')
 source.write_bytes((REPAIRS/'final-c3-supplement-r2.source.txt').read_bytes())
 out=driver.EVIDENCE/'eqn-supplement-r2'
 need(not out.exists(), 'do not overwrite evidence')
 out.mkdir()
 for name in FILES:
  (out/name).write_bytes((REPAIRS/name).read_bytes())
 (out/'run_final_c3_r2_once.py').write_bytes(Path(__file__).read_bytes())
 (out/'library-object-fingerprints-before.json').write_text(json.dumps(ctx.library_objects,indent=2)+'\n')
 argv=[sys.executable,'-I',str(driver.CHECKER),str(out/'native'),manifest['probe_module'],manifest['native_label']]
 (out/'launch.json').write_text(json.dumps({'argv':argv,'cwd':str(ROOT),'driver_sha256':DRIVER_SHA,'adapter_sha256':ADAPTER_SHA,'head':ctx.pins['head'],'base':ctx.pins['base'],'before_freeze_verified':True},indent=2)+'\n')
 proc=subprocess.run(argv,cwd=ROOT)
 driver.assert_frozen(ctx)
 for name,digest in FILES.items():
  need(sha((REPAIRS/name).read_bytes())==digest, 'proposal changed during native check')
 need(source.read_bytes()==(REPAIRS/'final-c3-supplement-r2.source.txt').read_bytes(), 'native source changed')
 (out/'after.json').write_text(json.dumps({'checker_returncode':proc.returncode,'after_freeze_verified':True,'head':ctx.pins['head'],'base':ctx.pins['base'],'source_sha256':sha(source.read_bytes()),'c3_census_disposition':'NOT_EXTRACTED_NO_CLEARANCE'},indent=2)+'\n')
 sys.exit(proc.returncode)

if __name__=='__main__':
 main()
