import contextlib
import gzip
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from scripts import dataset_stats
from scripts.dataset_shards import package


class DatasetStatsTests(unittest.TestCase):
    def test_shards_only_summary_and_render(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'data.jsonl'
            records = [
                dict(id='a', source_module='TCSlib.BooleanAnalysis.Basic',
                     proof_complete=True, statement_source='citation',
                     proof_source='lean', difficulty=0),
                dict(id='b', source_module='TCSlib.GraphTheory.Basic',
                     proof_complete=False, statement_source='lean', proof_source='none'),
                dict(id='c', source_module='TCSlib.BooleanAnalysis.Basic',
                     proof_complete=True, proof_source='citation', difficulty=2),
            ]
            source.write_text(''.join(json.dumps(r) + '\n' for r in records))
            plain = dataset_stats.compute(source)
            compressed = root / 'data.jsonl.gz'
            with gzip.open(compressed, 'wt') as handle:
                handle.write(source.read_text())
            self.assertEqual(dataset_stats.compute(compressed)['n_records'], 3)
            manifest = root / 'data.manifest.json'
            packaged = package(source, manifest, max_bytes=230)
            self.assertGreater(len(packaged['shards']), 1)
            source.unlink()
            compressed.unlink()

            with patch.object(dataset_stats, '_file_date', wraps=dataset_stats._file_date) as date:
                sharded = dataset_stats.compute(source)
                date.assert_called_once_with(manifest)
            for key in plain.keys() - {'size_mb'}:
                self.assertEqual(sharded[key], plain[key], key)
            self.assertEqual(sharded['n_complete'], 2)
            self.assertEqual(sharded['n_rated'], 2)
            self.assertEqual(sharded['n_statement_cited'], 1)
            self.assertEqual(sharded['n_proof_none'], 1)
            self.assertEqual(sharded['size_mb'], round(sum(
                s['compressed_bytes'] for s in packaged['shards']) / 1e6))

            for requested in [source, compressed, manifest]:
                page = root / 'index.html'
                page.write_text('%%n_records%% records; %%n_complete%% complete; %%size_mb%% MB')
                output = root / 'stats.json'
                with contextlib.redirect_stdout(io.StringIO()):
                    result = dataset_stats.main([
                        '--dataset', str(requested), '--render', str(page),
                        '--json', str(output),
                    ])
                self.assertEqual(result, 0)
                self.assertEqual(json.loads(output.read_text()), sharded)
                self.assertEqual(page.read_text(), '3 records; 2 complete; 0 MB')

    def test_missing_dataset_reports_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            with contextlib.redirect_stderr(io.StringIO()) as errors:
                result = dataset_stats.main(['--dataset', str(Path(tmp) / 'missing.jsonl')])
            self.assertEqual(result, 1)
            self.assertIn('not found', errors.getvalue())


if __name__ == '__main__':
    unittest.main()
