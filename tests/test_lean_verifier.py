"""Small verifier regression fixtures; synthetic binaries never enter Lean.

Run: python -B tests/test_lean_verifier.py
These tests check cache/receipt validation, not mathematical theorems.
"""
from copy import deepcopy
from contextlib import contextmanager
from pathlib import Path
import shutil
import sys
import unittest
from uuid import uuid4

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
TEMP_ROOT = ROOT / "lean/.build/verifier-test-tmp"
sys.path.insert(0, str(ROOT / "lean"))
import verification_core as verifier


@contextmanager
def fixture_directory(prefix):
    # Python 3.13's Windows TemporaryDirectory(0700) conflicts with some
    # restricted-token runners. A normal workspace mkdir inherits its ACL.
    path = TEMP_ROOT / (prefix + uuid4().hex)
    path.mkdir()
    try:
        yield path
    finally:
        if path.resolve().parent != TEMP_ROOT.resolve():
            raise ValueError("Fixture cleanup escaped its dedicated directory")
        shutil.rmtree(path)


class VerificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = verifier.load_plan(ROOT / "lean/ARD2")
        TEMP_ROOT.mkdir(parents=True, exist_ok=True)

    def test_all_exact_source_closures(self):
        expected = {"shared": 35, "Y": 189, "RPD": 36, "LRD": 41,
                    "Omega-LRD3": 44, "ARD": 56, "ARD-legacy": 50, "IPD": 55, "ARD2": 51}
        for scope, count in expected.items():
            with self.subTest(scope=scope):
                plan = verifier.load_plan(ROOT / "lean" / scope)
                self.assertEqual(len(plan["ordered"]), count)
        self.assertEqual(len(verifier.load_plan(ROOT / "lean")["ordered"]), 330)

    def test_all_import_sidecars_affect_environment(self):
        with fixture_directory("lean-artifact-test-") as name:
            root = Path(name)
            for suffix in verifier.IMPORT_SUFFIXES:
                verifier.module_artifact(root, "Foo", suffix).write_bytes(b"fixture")
            baseline = verifier.artifact_tree(root)
            self.assertEqual(baseline["olean_files"], 1)
            self.assertEqual(baseline["import_sidecars"], 4)
            for suffix in verifier.IMPORT_SUFFIXES:
                with self.subTest(suffix=suffix):
                    path = verifier.module_artifact(root, "Foo", suffix)
                    path.write_bytes(b"changed fixture")
                    self.assertNotEqual(baseline["sha256"], verifier.artifact_tree(root)["sha256"])
                    path.write_bytes(b"fixture")
            (root / "lean.exe").write_bytes(b"compiler fixture")
            self.assertNotEqual(baseline["sha256"], verifier.artifact_tree(root, include_runtime=True)["sha256"])

    def test_module_bundle_and_exact_clear(self):
        with fixture_directory("lean-bundle-test-") as name:
            root = Path(name)
            (root / "Namespace").mkdir()
            for module in ("Namespace.Foo", "Namespace.Bar"):
                for suffix in verifier.IMPORT_SUFFIXES:
                    verifier.module_artifact(root, module, suffix).write_bytes(b"fixture")
            self.assertEqual(set(verifier.module_bundle(root, "Namespace.Foo")), set(verifier.IMPORT_SUFFIXES))
            verifier.clear_module_bundle(root, "Namespace.Foo")
            self.assertEqual(verifier.module_bundle(root, "Namespace.Foo"), {})
            self.assertEqual(len(verifier.module_bundle(root, "Namespace.Bar")), 5)

    def test_external_proof_shadowing_rejected(self):
        with fixture_directory("lean-shadow-test-") as name:
            root = Path(name)
            module = self.plan["ordered"][0]
            path = verifier.module_artifact(root, module, ".olean.private")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"not an actual Lean artifact")
            with self.assertRaisesRegex(ValueError, "contains local proof"):
                verifier.external_environment([root], self.plan)

    def test_axiom_logs_are_named_and_complete(self):
        good = "'Example.ok' depends on axioms: [propext, Classical.choice]\n"
        self.assertEqual(verifier.parse_reports(good, ["ok"])[0]["name"], "Example.ok")
        for text, names in ((good, ["other"]), (good, ["ok", "missing"]),
                            ("'ok' depends on axioms: [sorryAx]", ["ok"]),
                            ("'ok' depends on axioms: [UnprovedAssumption]", ["ok"])):
            with self.subTest(text=text, names=names), self.assertRaises(ValueError):
                verifier.parse_reports(text, names)

    def test_current_old_style_import_syntax(self):
        # The published 310 sources use old-style / public imports. This
        # fixture intentionally makes no modern meta/import-all support claim.
        text = """/- ignored import Hidden.A /- nested -/ -/
import Base.One Base.Two -- trailing comment
public import Visible.Three
-- import Hidden.B
#print axioms result
"""
        self.assertEqual(verifier.imports(text), ["Base.One", "Base.Two", "Visible.Three"])
        self.assertEqual(verifier.requested_reports(text), ["result"])

    def synthetic_receipt(self, output, logs):
        """Shape fixture only: bytes/logs are intentionally not compiled proof evidence."""
        plan = self.plan
        tree = {"sha256": "a" * 64, "olean_files": 1, "import_sidecars": 4,
                "runtime_binaries": 1, "bytes": 42}
        environment = {"policy": verifier.POLICY,
                       "verifier_sha256_lf": verifier.file_hash(verifier.CORE, lf=True),
                       "compiler_version_output": "Lean (version 4.33.1, fixture)\n",
                       "compiler_executable_sha256": "b" * 64,
                       "actual_compiler_sha256": "c" * 64,
                       "lean_sysroot_artifacts": tree,
                       "dependency_revisions": verifier.dependency_revisions(plan),
                       "external_artifact_trees": [tree]}
        fingerprints = verifier.module_fingerprints(plan, environment)
        receipt = {"schema_version": 2, "policy": verifier.POLICY, "complete": True,
                   "project": "ARD2", "targets": plan["targets"], "inputs": plan["inputs"],
                   "closure_sha256": plan["closure_sha256"], "owner_inputs": plan["owner_inputs"],
                   "environment": environment, "compiler": environment["compiler_version_output"].strip(),
                   "modules": {}, "total_proof_modules": len(plan["ordered"]),
                   "fresh_modules": len(plan["ordered"]), "reused_modules": 0, "axiom_reports": 0}
        for module in plan["ordered"]:
            target = verifier.module_artifact(output, module, ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b"synthetic verifier-test bytes; never given to Lean")
            names = plan["requested"][module]
            text = "".join(f"'{name}' does not depend on any axioms\n" for name in names)
            log = logs / (module + ".log")
            log.write_text(text, encoding="utf-8")
            reports = verifier.parse_reports(text, names)
            receipt["modules"][module] = {
                "fingerprint": fingerprints[module], "olean_sha256": verifier.file_hash(target),
                "artifact_bundle": verifier.module_bundle(output, module),
                "log_sha256_lf": verifier.file_hash(log, lf=True), "reports": reports,
                "axiom_reports": len(reports), "certification": "fresh-source-compilation"}
            receipt["axiom_reports"] += len(reports)
        return receipt

    def test_receipt_rejects_stale_or_inconsistent_records(self):
        with fixture_directory("lean-receipt-test-") as name:
            output, logs = Path(name) / "artifacts", Path(name) / "logs"
            output.mkdir()
            logs.mkdir()
            receipt = self.synthetic_receipt(output, logs)
            verifier.validate_receipt(self.plan, receipt, artifacts=output, logs=logs)
            cases = []
            stale = deepcopy(receipt)
            stale["complete"] = False
            cases.append(stale)
            stale = deepcopy(receipt)
            stale["inputs"] = {}
            cases.append(stale)
            stale = deepcopy(receipt)
            stale["environment"]["actual_compiler_sha256"] = ""
            cases.append(stale)
            stale = deepcopy(receipt)
            stale["environment"]["lean_sysroot_artifacts"].pop("import_sidecars")
            cases.append(stale)
            stale = deepcopy(receipt)
            stale["reused_modules"] = 1
            cases.append(stale)
            stale = deepcopy(receipt)
            stale["modules"].pop(self.plan["ordered"][0])
            cases.append(stale)
            for index, stale in enumerate(cases):
                with self.subTest(case=index), self.assertRaises(ValueError):
                    verifier.validate_receipt(self.plan, stale, artifacts=output, logs=logs)
            module = self.plan["ordered"][0]
            verifier.module_artifact(output, module, ".olean.private").write_bytes(b"unexpected sidecar")
            with self.assertRaisesRegex(ValueError, "compiled artifact"):
                verifier.validate_receipt(self.plan, receipt, artifacts=output, logs=logs)

    def test_project_output_lock_is_exclusive(self):
        with fixture_directory("lean-lock-test-") as name:
            root = Path(name)
            with verifier.project_lock(root):
                with self.assertRaisesRegex(ValueError, "locked"):
                    with verifier.project_lock(root):
                        self.fail("Second writer acquired the project output")
            self.assertFalse((root / ".build/verification.lock").exists())

    def test_dependency_fingerprints_ignore_unrelated_project_metadata(self):
        plan = deepcopy(self.plan)
        baseline = verifier.module_fingerprints(plan, {"test_environment": True})
        plan["owner_inputs"]["FutureNotation"] = {"unrelated": "f" * 64}
        self.assertEqual(baseline, verifier.module_fingerprints(plan, {"test_environment": True}))
        plan["owner_inputs"]["shared"]["test-changed-shared-config"] = "f" * 64
        self.assertNotEqual(baseline, verifier.module_fingerprints(plan, {"test_environment": True}))


if __name__ == "__main__":
    unittest.main(verbosity=2)
