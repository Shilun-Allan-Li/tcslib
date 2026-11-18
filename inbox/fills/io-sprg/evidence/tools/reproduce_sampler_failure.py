# io-sprg reproducibility check for an overwritten historical failed log.
# Root only; swaps only an untracked probe copy, always restoring current bytes.
import hashlib,json,os,pathlib,subprocess
root=pathlib.Path.cwd();run=root/'evidence/rule10/m0_final'
mod='evidence/probes/io_sprg_m0_final/seals_coe_A/SealA_Cryptography_Obfuscation_StructuredSeed_Samplers'
probe=root/(mod+'.lean');current=probe.read_bytes()
old=run/'failed-sampler-seal-source/coe-A/SealA_Cryptography_Obfuscation_StructuredSeed_Samplers.lean.txt'
order=run/'orders/reproduce-sampler.txt';order.write_text(mod+'\n')
prior=[json.loads(l) for l in(run/'seal-runs/results.jsonl').read_text().splitlines()]
oldrec=next(r for r in prior if r.get('module')==mod and r['rc']==1)
try:
 probe.write_bytes(old.read_bytes())
 out=run/'reproduction-original-sampler'
 subprocess.run(['python3','-I','evidence/tools/seal/runner_full.py',str(root),str(order),str(root/'.lake/io-sprg-oleans'),str(out)],check=True)
 rows=[json.loads(l) for l in(out/'results.jsonl').read_text().splitlines()]
 rec=next(r for r in reversed(rows) if r.get('module')==mod)
 assert rec['rc']==1 and rec['errors']==2,rec
 log=out/'mods'/(mod.replace('/','_')+'.log');digest=hashlib.sha256(log.read_bytes()).hexdigest()
 archive=run/'log-archive';archive.mkdir(exist_ok=True)
 (archive/(digest+'.log')).write_bytes(log.read_bytes())
 (out/'comparison.json').write_text(json.dumps(dict(expected_old_log_sha256=oldrec['log_sha256'],reproduction_sha256=digest,exact_log_reproduced=digest==oldrec['log_sha256'],same_two_failures=True,original_probe_sha256=oldrec['source_sha256'],reproduced_probe_sha256=rec['source_sha256'],reason='The retry overwrote the old log. Saved old probe/source metadata is retained; this explicitly dated reproduction restores diagnostic evidence.'),indent=2)+'\n')
 print('ORIGINAL_FAILURE_REPRODUCED errors=2 exact_log='+str(digest==oldrec['log_sha256']),flush=True)
finally:
 probe.write_bytes(current)
 assert probe.read_bytes()==current
