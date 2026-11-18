"""Verifier rejection tests; these mocks are not proof-verification receipts."""
import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

spec=importlib.util.spec_from_file_location('pera_verify',Path(__file__).with_name('verify.py'))
module=importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

class VerificationGateTests(unittest.TestCase):
    def fixture(self,root):
        (root/'PeraVerification').mkdir()
        for name in ('PeraVerification.lean','Audit.lean'):
            (root/name).write_text('-- test fixture only\n')
        (root/'lean-toolchain').write_text('leanprover/lean4:v4.24.0\n')
        (root/'lake-manifest.json').write_text('{}')
        (root/'lakefile.toml').write_text('name = "fixture"\n')
        (root/'theorems.json').write_text(json.dumps(['PeraVerification.testTheorem']))

    def test_missing_or_untrusted_axiom_audit_fails_even_when_commands_succeed(self):
        for audit in ('',"'PeraVerification.testTheorem' depends on axioms: [sorryAx]",
                      "'Other.theorem' depends on axioms: [propext]"):
            with self.subTest(audit=audit),tempfile.TemporaryDirectory() as temp:
                root=Path(temp);self.fixture(root)
                replies=[SimpleNamespace(returncode=0,stdout=x) for x in ('build ok',audit,'Lean 4.24.0')]
                with patch.object(module,'HERE',root),patch.object(module.subprocess,'run',side_effect=replies):
                    with self.assertRaises(RuntimeError):module.verify(root/'out')
                self.assertEqual(json.loads((root/'out/result.json').read_text())['status'],'verification_failed')

    def test_proof_escape_is_rejected_before_any_command(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);self.fixture(root)
            (root/'PeraVerification/Bad.lean').write_text('theorem bad : False := by sorry\n')
            with patch.object(module,'HERE',root),patch.object(module.subprocess,'run') as call:
                with self.assertRaises(ValueError):module.verify(root/'out')
                call.assert_not_called()

    def test_nonzero_build_cannot_be_reported_verified(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);self.fixture(root)
            with patch.object(module,'HERE',root),patch.object(module.subprocess,'run',return_value=SimpleNamespace(returncode=1,stdout='build failed')):
                with self.assertRaises(RuntimeError):module.verify(root/'out')
            result=json.loads((root/'out/result.json').read_text())
            self.assertEqual(result['status'],'verification_failed')
            self.assertEqual(result['command_exit_codes'],{'build':1})

if __name__=='__main__':unittest.main()
