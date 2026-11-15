#!/usr/bin/env python3
"""Finish controls, true-base seals, restoration, full final sweep and final probes serially."""
import json
from pathlib import Path
import subprocess
import sys

def run(cmd,allow_failure=False):
 with Path('evidence/logs/remaining-validation.log').open('a')as log:
  line='RUN '+repr(cmd)+'\n';print(line,end='',flush=True);log.write(line);log.flush()
  p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,bufsize=1)
  for line in p.stdout:
   print(line,end='',flush=True);log.write(line);log.flush()
  rc=p.wait();line='EXIT '+str(rc)+'\n';print(line,end='',flush=True);log.write(line)
  if rc and not allow_failure:raise RuntimeError((cmd,rc))
 return rc

def records(phase,count,seals=False):
 rows=[json.loads(l)for l in Path('evidence/logs',phase,'results.jsonl').read_text().splitlines()]
 assert len(rows)==count,(phase,len(rows),count)
 for r in rows:
  assert r['exit']in ([0,1]if seals else [0]),r
  assert (r['exit']==0)==(r['errors']==0),r
 return rows

records('seals-final',56,True)
run(['python3','-I','evidence/tools/run_check.py','--phase','seals-final-correction-01',
     '--order','evidence/seals/final/correction1-order.txt','--continue-on-error'],True)
corrected=records('seals-final-correction-01',10,True)
assert corrected[0]['exit']==0 and corrected[1]['exit']==0
assert all(r['exit']==0 for r in corrected if '_A_'in r['module'])
run(['python3','-I','evidence/tools/run_check.py','--phase','seal-controls',
     '--order','evidence/seals/controls/order.txt','--continue-on-error'],True)
controls=records('seal-controls',8,True)
manifest=json.loads(Path('evidence/seals/controls/manifest.json').read_text())
for expected,actual in zip(manifest,controls):
 assert actual['module']==expected['probe'][:-5]
 assert actual['errors']==expected['expected_errors'],(expected,actual)
Path('evidence/seals/controls/verified.txt').write_text(
 'PASS: four unsealed positives; four sealed negatives, each with exactly one error.\n')

base_modules={
'TCSlib/Complexity/CircuitComplexity/DAGCircuit',
'TCSlib/Cryptography/SecureComputation/Garbling',
'TCSlib/Cryptography/SecureComputation/SpecialEncryptionSecurity',
'TCSlib/Cryptography/SecureComputation/SpecialEncryptionMulti',
'TCSlib/Cryptography/SecureComputation/GarblingSpecial',
'TCSlib/Cryptography/SecureComputation/GarblingSecurity',
'TCSlib/Cryptography/SecureComputation/Yao',
'TCSlib/Cryptography/SecureComputation/YaoReal',
'TCSlib/Cryptography/SecureComputation'}
issued=Path('evidence/issued/order.txt').read_text().splitlines()
order=[m for m in issued if m in base_modules]
assert len(order)==9
Path('evidence/seals/base-bootstrap-order.txt').write_text(''.join(m+'\n'for m in order))
switched=False
try:
 run(['python3','-I','evidence/tools/switch_sources.py','base']);switched=True
 run(['python3','-I','evidence/tools/run_check.py','--phase','base-seal-environment',
      '--order','evidence/seals/base-bootstrap-order.txt'])
 records('base-seal-environment',9)
 run(['python3','-I','evidence/tools/run_check.py','--phase','seals-base',
      '--order','evidence/seals/base/order.txt','--continue-on-error'],True)
 records('seals-base',24,True)
finally:
 if switched:run(['python3','-I','evidence/tools/switch_sources.py','final'])
run(['python3','-I','evidence/tools/run_check.py','--phase','final-sweep',
     '--order','evidence/final-order.txt'])
rows=records('final-sweep',174)
assert sum(r['sorries']for r in rows)==25
assert sum(r['sorries']>0 for r in rows)==11
run(['python3','-I','evidence/tools/run_check.py','--phase','final-probes',
     'evidence/probes/FinalMeta','evidence/probes/FinalSignatures',
     'evidence/probes/ExplicitUnfoldMeta'])
records('final-probes',3)
Path('evidence/logs/remaining-validation-PASS.txt').write_text(
 'PASS: controls; baseline seals; exact source restoration; 174-module final sweep, '
 'zero errors, 25 admissions in 11 modules; all final metadata probes.\n')
print('REMAINING VALIDATION COMPLETED',flush=True)
