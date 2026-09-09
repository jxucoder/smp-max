"""Exercise certificate runner control flow with deterministic fake tools.

These tests cover expected solver exit 20, failed checkers, and artifact
retention. They do not simulate or claim mathematical certificate checks.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
FAKE_TOOL = '''#!/usr/bin/env python3
import os,sys
from pathlib import Path
role=Path(sys.argv[0]).name
failure=os.environ.get('SMP_TEST_FAILURE','')
if role=='exporter':
    for i in range(120):Path(f'cubeL{i:03d}.cnf').write_text('p cnf 1 2\\n1 0\\n-1 0\\n')
elif role=='kissat':
    Path(sys.argv[-1]).write_text('test drat')
    sys.exit(10 if failure=='SAT' else 20)
elif role=='drat-trim':
    Path(sys.argv[-1]).write_text('test lrat')
    print('s NOT VERIFIED' if failure=='trim' else 's VERIFIED')
elif role=='cake-lpr':
    print('s NOT VERIFIED' if failure=='cake-verdict' else 's VERIFIED UNSAT')
    sys.exit(1 if failure=='cake-exit' else 0)
'''


class CertificateRunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        for role in ['exporter', 'kissat', 'drat-trim', 'cake-lpr']:
            tool = self.directory / role
            tool.write_text(FAKE_TOOL)
            tool.chmod(0o755)

    def run_pipeline(self, failure='', *extra):
        out = self.directory / ('run-' + (failure or 'success'))
        command = [sys.executable, str(ROOT / 'tools/verify_five_cubes.py'), '--output-dir', str(out)]
        for role in ['exporter', 'kissat', 'drat-trim', 'cake-lpr']:
            command.extend(['--' + role, str(self.directory / role)])
        command.extend(['--cubes', '0', *extra])
        result = subprocess.run(command, cwd=self.directory, text=True, capture_output=True,
                                env={**os.environ, 'SMP_TEST_FAILURE': failure})
        return out, result

    def test_expected_unsat_records_success_then_deletes_proofs(self):
        out, result = self.run_pipeline()
        self.assertEqual(result.returncode, 0, result.stderr)
        record = json.loads((out / 'verification.jsonl').read_text())
        self.assertEqual(record['solver_rc'], 20)
        self.assertEqual(record['verdict'], 's VERIFIED UNSAT')
        self.assertEqual(len(record['lrat_sha256']), 64)
        self.assertTrue((out / 'cubeL000.cnf').exists())
        self.assertFalse((out / 'cubeL000.lrat').exists())
        self.assertFalse((out / 'cubeL000.drat').exists())
        self.assertIn('This subset alone does not establish the upper bound', result.stdout)

    def test_sat_and_failed_checkers_stop_without_recording_success(self):
        for failure in ['SAT', 'trim', 'cake-verdict', 'cake-exit']:
            with self.subTest(failure=failure):
                out, result = self.run_pipeline(failure)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual((out / 'verification.jsonl').read_text(), '')
                self.assertTrue((out / 'cubeL000.drat').exists())
                if failure != 'SAT':
                    self.assertTrue((out / 'cubeL000.lrat').exists())

    def test_keep_proofs_preserves_successful_artifacts(self):
        out, result = self.run_pipeline('', '--keep-proofs')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((out / 'cubeL000.lrat').exists())
        self.assertTrue((out / 'cubeL000.drat').exists())


if __name__ == '__main__':
    unittest.main()
