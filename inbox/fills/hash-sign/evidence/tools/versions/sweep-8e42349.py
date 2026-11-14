import datetime
import json
import pathlib
import re
import subprocess
import sys

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
checker = ev / 'tools/check_module.py'
order = (ev / 'logs/extended-order.txt').read_text().splitlines()
start_index = int(sys.argv[1]) if len(sys.argv) > 1 else 0
with (ev / 'logs/sweep-results.jsonl').open('a') as ledger:
    for index, module in enumerate(order):
        if index < start_index:
            continue
        label = 'sweep/' + f'{index:03d}_' + module.replace('/', '_')
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        p = subprocess.run(['python3', '-I', str(checker), module, label], cwd=repo, stdout=subprocess.DEVNULL)
        end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        text = (ev / 'logs' / (label + '.log')).read_text()
        rss = re.search(r'(\d+)\s+maximum resident set size', text)
        record = dict(index=index, module=module, start=start, end=end, exit=p.returncode,
            max_rss_bytes=int(rss[1]) if rss else None, log='logs/' + label + '.log')
        print(json.dumps(record), file=ledger, flush=True)
        print(index, module, p.returncode, flush=True)
        if p.returncode:
            raise SystemExit(p.returncode)
