"""Retain the concrete published-provider searches used in the cp2 report."""
import datetime
import json
from pathlib import Path
import subprocess

root = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
evidence = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
queries = [
    ('published probability and simulation providers',
     ['rg', '-n', 'expect_sample_pair|prob_sample_pair|expect_sample_comm|expect_sample_coord|expect_simulate_congr',
      'TCSlib/Cryptography/Games']),
    ('codec extensionality provider',
     ['rg', '-n', 'MachineCodec.*ext|theorem.*codec.*ext|structure MachineCodec',
      'TCSlib/Cryptography/Games']),
    ('codec extensionality in completed canonical-base runtime catalogs',
     ['rg', '-n', r'MachineCodec\.ext',
      str(evidence / 'logs/helper-checks/Inventory-baseauth-cp2-r1-inventory1.log'),
      str(evidence / 'logs/readers-01/LamportEvidence_Seals_Base_Inventory.log')]),
    ('cost-zero return provider',
     ['rg', '-n', 'costBoundedBy.*zero|CostBoundedBy.*0|exists_pure_of_cost_zero',
      'TCSlib/Cryptography/Games']),
    ('tuple encoding injectivity outside the owned helpers',
     ['rg', '-n', '--glob', '!**/Signatures/Lamport/**',
      'encodeList_(injective|eq_iff|ofFn_eq_iff)', 'TCSlib/Cryptography']),
    ('two-block overlap and public reader providers',
     ['rg', '-n', 'ofFn_blocks_two_symm|flatten_ofFn_two|ofFn_blocks_symm',
      'TCSlib/Cryptography/Asymptotic/OneWay.lean']),
]
records = []
for description, command in queries:
    result = subprocess.run(command, cwd=root, capture_output=True, text=True)
    if result.returncode not in (0, 1):
        raise RuntimeError(result.stderr)
    records.append(dict(description=description, command=command, status=result.returncode,
                        stdout=result.stdout, stderr=result.stderr))
destination = evidence / 'logs' / 'duplication-searches-checkpoint2.json'
destination.write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                      root=str(root), searches=records), indent=2) + '\n')
print(destination)
for record in records:
    print(record['description'], 'status=' + str(record['status']),
          'matching-lines=' + str(len(record['stdout'].splitlines())))
