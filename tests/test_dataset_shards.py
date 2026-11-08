import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from proofmatch.dataset_io import open_dataset, resolve_dataset
from scripts.dataset_shards import package, verify


class ShardTests(unittest.TestCase):
    def test_round_trip_limits_and_chunked_reads(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'data.jsonl'
            raw = ''.join(json.dumps({'id': str(i), 'text': hashlib.sha256(str(i).encode()).hexdigest()}) + '\n'
                          for i in range(100))
            source.write_text(raw)
            manifest = root / 'data.manifest.json'
            result = package(source, manifest, max_bytes=700)
            self.assertGreater(len(result['shards']), 1)
            self.assertEqual(verify(manifest)['rows'], 100)
            self.assertEqual(resolve_dataset(source), manifest)
            for size in [1, 7, 1000, -1]:
                with open_dataset(source) as handle:
                    chunks = []
                    while chunk := handle.read(size):
                        chunks.append(chunk)
                    self.assertEqual(''.join(chunks), raw)
            with open_dataset(source) as handle:
                self.assertEqual(list(handle), raw.splitlines(keepends=True))
            with open_dataset(source) as handle:
                self.assertEqual(handle.readline(3), raw[:3])
                self.assertEqual(handle.read(), raw[3:])
            source.unlink()
            with open_dataset(root / 'data.jsonl.gz') as handle:
                self.assertEqual(handle.read(), raw)
            shard = root / result['shards'][0]['path']
            data = bytearray(shard.read_bytes()); data[12] ^= 1; shard.write_bytes(data)
            with self.assertRaisesRegex(ValueError, 'checksum'):
                verify(manifest)

    def test_multiline_header_context_and_unused_identifier_ranges(self):
        from scripts.build_dataset import declared_short_name, parse_file_context
        from scripts.build_dep_graph import parse_ilean
        self.assertEqual(declared_short_name('private theorem\n  continued_name : True := by trivial'), 'continued_name')
        lines = ['open Foo (a', '  b)', 'theorem bar : True := by trivial']
        preamble, contexts, _ = parse_file_context(lines)
        self.assertEqual(preamble, [('', 'open Foo (a\n  b)')])
        self.assertIn(2, contexts)
        from scripts.dataset_check import formal_context_lines, leaked_line
        self.assertFalse(any(map(leaked_line, formal_context_lines("\n".join(lines)))))
        self.assertTrue(any(map(leaked_line, formal_context_lines("open a prose sentence (\nmissing"))))
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Test.ilean'; source = path.with_suffix('.lean')
            source.write_text('theorem Set.foo : True :=\n  True.intro\n')
            path.write_text(json.dumps({'module': 'TCSlib.Test', 'references': {
                json.dumps({'c': {'m': 'TCSlib.Test', 'n': 'Set.foo'}}): {
                    'definition': [0, 8, 0, 15], 'usages': []}}}))
            decl = parse_ilean(path, source)['declarations']['Set.foo']
            self.assertEqual((decl['startLine'], decl['endLine']), (1, 2))


if __name__ == '__main__':
    unittest.main()
