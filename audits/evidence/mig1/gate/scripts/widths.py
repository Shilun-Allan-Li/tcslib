"""Report lines longer than 100 Unicode characters. Usage: python3 -I widths.py <file> ..."""
import sys
bad = 0
for p in sys.argv[1:]:
    for i, l in enumerate(open(p, encoding='utf-8').read().split('\n'), 1):
        if len(l) > 100:
            bad += 1
            print(f'{p}:{i}: {len(l)} characters')
print(f'lines over 100 characters: {bad}')
