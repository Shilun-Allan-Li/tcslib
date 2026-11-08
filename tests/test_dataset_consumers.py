"""Exercise dataset consumers without a complete JSONL or gzip mirror."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from proofmatch.catalog import BlueprintBinding, load_blueprint_candidates
from proofmatch.models import DocumentBlock, DocumentIndex
from proofmatch.search import search_candidates
from proofmatch.upstream import _target_record
from scripts import dataset_check, dataset_hygiene, dataset_pipeline
from scripts import dataset_splice, reference_coverage, sources, view_dataset
from scripts.dataset_shards import package


class DatasetConsumerTests(unittest.TestCase):
    def test_shards_only_readers(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = Path(tmp) / 'data.jsonl'
            records = [dict(id='Test.foo', title='Test', kind='theorem',
                            source_module='TCSlib.Test', statement_source='lean',
                            informal_statement='A test statement.', proof='by trivial')]
            source.write_text(''.join(json.dumps(r) + '\n' for r in records))
            package(source, source.with_suffix('.manifest.json'))
            source.unlink()
            for loader in [dataset_check.load, reference_coverage.load_records,
                           sources.load_records]:
                with self.subTest(loader=loader.__module__):
                    self.assertEqual(loader(source), records)
            self.assertEqual(view_dataset.load(source, None), records)
            self.assertEqual(dataset_splice.load_patch(source), {'Test.foo': records[0]})
            self.assertEqual(dataset_pipeline.dataset_modules(source), {'TCSlib.Test': 1})
            self.assertEqual(list(dataset_hygiene.from_dataset(source))[0][0], 'Test.foo')
            self.assertEqual(_target_record(source, 'Test.foo'), records[0])
            bindings = {'Test.foo': BlueprintBinding('Test.foo', Path('chapter.tex'))}
            self.assertEqual(load_blueprint_candidates(source, bindings)[0].lean_name, 'Test.foo')
            index = DocumentIndex('test', (DocumentBlock(
                'block', 1, 1, 'theorem', 'Test', 'A test statement.', 1.0),), ())
            self.assertEqual(search_candidates(index, source)[0].lean_name, 'Test.foo')
            with patch('sys.argv', ['view_dataset.py', str(source), '--print', '1']):
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertNotEqual(view_dataset.main(), 1)


if __name__ == '__main__':
    unittest.main()
