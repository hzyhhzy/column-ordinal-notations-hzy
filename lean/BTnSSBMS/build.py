"""Bounded, dependency-free Lean build for this independent project.

Only the Lean distribution is imported. No previous notation project's
verification record or build output is changed. A successful build certifies
the theorems actually present, not the still-unformalized paper theorem.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
MODULES = ["Syntax", "Parents", "BMS", "ParentChains", "Activation", "ParentValues",
           "Keys", "SourceFS", "SourceHead",
           "Decoding", "KeyEquality", "KeyOrder", "Encoder", "Environment",
           "FrameOrder", "FrameHeight", "FrameReferences", "BindingAnchors", "KeyLevels", "Order", "BMSDescent",
           "SearchGeometry", "NumericalLegality", "FirstDiagonal", "BMSBlocks", "CopyRebase",
           "RowGeometry", "NumericalTransport", "ViewExtension", "AuxiliaryParents", "ForestFence",
           "ForestScope", "NumericalScope", "NumericalUnits",
           "KeyParentGeometry", "FrameAncestry", "KeyEntries", "KeyForestScope", "KeyScope",
           "FullLegality", "SourceLegality", "KeyParentTypes", "NumericalKinds", "SourcePruning", "SourceCopyHead", "NumericalOrder", "SourceSeeds", "SourceZero",
           "CopyHistory", "CopyBody", "CopyEntry", "KeyNormalizationOrder", "EncoderHeadOrder",
           "EncoderBoundary", "EncoderHeadState", "EncoderOrderScope", "EncoderStrictOrder", "CopySeam", "CopyAnnotation",
           "CopyDonation", "CopySplice", "CopyHole", "CopyRoot", "CopyIteration",
           "DonationMaterial", "DonationIteration", "SourceRootSearch",
           "SourceSpine", "SourceSpineHole", "SourceTopScope", "SourceTopSelection",
           "SourceAnnotatedSpine", "SourceMarkedSpine", "SourceParentPrefix",
           "SourceRootHole", "SourceRootCoordinates", "SourceLowAssembly",
           "SourceTopAncestry", "SourceMarkedHistory", "SourceHighAssembly",
           "SourceTopExistence", "SourceLowLeaf", "SourceZeroGeometry", "SourceZeroSelection",
           "SourceZeroAssembly", "SourceFiniteClosure", "ForestSlotLeaves", "EncoderHeadTypes",
           "BindingSources", "EncoderBindingSources", "PartialRebaseEntry", "CopyKeyTransport", "PartialRebaseComparison",
           "ClosedForestTransplant", "NumericalRelocation", "RelocationComposition", "RelocationOrder",
           "RelocationLegality", "TransplantNaturality", "CrossEntryKeyTransport", "CopyKeyComparison",
           "BindingMaterials", "EncoderBindingMaterials", "QueryMaterialTransport", "QueryCopyTransport",
           "FrameCoupling", "MaterialStability", "ScopedFrameCoupling", "CoupledQuery", "CoupledSaving",
           "ControlTrace", "EncoderControlTransport", "EncoderFrameTransport", "CopyControlTransport",
           "FixedPrefixMaterials", "PartialRebaseQuery", "FixedPrefixCoupling", "PartialRebaseCoupling",
           "FixedPrefixControl", "PartialRebaseControl",
           "EncoderEntries", "EntrySoundness", "EntryExecution", "EntryOrigins",
           "EncoderEntryOrigins", "EntryRebaseControl", "EntryParentGeometry",
           "EntryFibers", "VisibleEntryFibers", "EncoderEntryFibers", "EntryOriginOrder",
           "EntryAncestry", "TargetPairControl", "EntryActivation", "EntryRebaseNumerics",
           "RowRebaseTrace", "RowRebaseValues", "EncoderRowTransport", "FixedPrefixRows",
           "PartialRebaseRows", "RebaseMatrixTransport",
           "BlockCutoff", "EntryBlockClosure", "RebaseBlockBoundary", "CompleteBlockTransport",
           "SourceBlocks", "SourceBlockCutoff", "SourceBlockEncoding", "SourceBlockTransport",
           "SourceEncodingOrder", "EntryOrder", "SourceBlockComparison", "DescendantBlocks", "ClosingBlockEncoding",
           "ClosingEntryOrigins", "ZeroEndpointClasses", "PositiveEndpointOrigins", "TopRowEndpointClasses",
           "FrameAncestorRecovery", "ClosingAncestorSources", "FramePersistence", "ClosingFrameExtension",
           "VisibleClosingOrigins", "ClosingKeyOrder",
           "FrameInsertion", "InsertionSaving", "ClosingQueryInsertion", "InsertionHead",
           "QueryAncestry", "QueryAncestorRecovery", "RekeyInsertion", "InsertionActivation",
           "KeySplice", "SplicedFrames", "SplicedSaving", "EncoderSpliceTransport",
           "ClosingRekey", "ClosingSpliceEntry", "ClosingSpliceTransport",
           "RootedSplice", "RootedFrames", "RootedSaving", "EncoderRootedTransport",
           "ClosingRootedEntry", "ClosingRootedTransport", "RootedQuery", "RootedSlots",
           "KeyRowRebase", "RootedHead", "ShiftedOutput", "RootedHeadComparison",
           "ShiftComparison", "FreshShift", "ClosingRowEntry", "RootedDecision",
           "RootedComparison", "ClosingInsertionComparison", "ClosingBlockSlice", "ClosingBlockComparison",
           "SourceStopTotality", "SourceTotality",
           "SourceLastOrder", "SourceLeafParents", "SourceCopyDescent", "SourceDescent",
           "SourceHW", "HWSplice", "HWTransport", "HWLowCopies", "HWHighCopies", "SourceHWClosure",
           "SourceBlockOrder", "SourceSiblingGeometry", "SourceBN", "BNDeletion", "BNLastChange",
           "BNSpecial", "BNPruning", "RelocationBlocks",
           "SiblingEntry", "SiblingRelocation", "SiblingComparison", "RelocationSuffix", "BNRelocation", "BNRootCopy",
           "TerminalSplice", "ZeroFloor", "BNSpliceZero", "BNSplice", "BNPositiveCopies", "SourceBNPositive",
           "BNDonation", "BNHighCopies", "SourceBNHigh", "ZeroCopyShape", "BNZeroSplice", "BNZeroCopies",
           "BNPrefixSplice", "BNZeroForest", "BNSpineLift", "SourceBNZero", "SourceBNClosure",
           "ExactNumericalPosition", "PartialRebaseHead", "PartialRebaseMaterial", "PartialRebaseNaturality",
           "ExactRelocationEntries", "PartialRebaseBlockComparison", "RelocatedRootMaterial",
           "PartialRebaseCopyComparison", "KeyEmptyExtension", "DonationInternalKey",
           "SourceSB", "SBBlockContext", "SBHistory", "SBDeletion",
           "SBCrossPhase", "SBCopyBarrier", "ExactAncestryReflection", "SBCopyAncestry",
           "ExactCopyHole", "SBCopyHoleBarrier", "ExactCopyBarrierPath", "SBCopyBarrierPosition",
           "SBConsecutiveCopies", "CopyRootChain",
           "CopyHoleSpan", "NumericalViewDensity", "CopyHoleDensity", "SBConsecutiveIntervals",
           "CopyHoleRun", "CopyRunBarrierPath", "SBSeparatedCopies",
           "CopyRunGeometry", "RootCopyReset", "RootCopyMaterial", "RootCopyBlock", "CopyRunRootBlock",
           "RelocationSplice", "RootedRelocation", "RebaseSplice", "RootCopySplice",
           "SpliceExtraction", "CopyRunSplicedMaterial", "CopyCountOrder", "CopySeamNaturality",
           "CopyHoleSquare", "CopyMaterialNaturality", "CopySeamSquare", "CopyRunNaturality", "CopyRunRebase",
           "Ceiling", "LastHole", "Coverage", "Fixtures",
           "SourceFixtures", "Audit"]


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=shutil.which("lean"))
    parser.add_argument("--seconds", type=int, default=120)
    parser.add_argument("--only", choices=MODULES)
    parser.add_argument("--publish", action="store_true")
    args = parser.parse_args()
    if not args.lean:
        parser.error("Lean 4.33.1 is required; pass --lean PATH or use lake env.")
    lean = str(Path(args.lean).resolve())
    version = subprocess.check_output([lean, "--version"], text=True, timeout=15).strip()
    if "version 4.33.1," not in version:
        raise SystemExit(f"Unexpected compiler: {version}")
    out = ROOT / ".build" / "lean"
    out.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(out))
    modules = MODULES[: MODULES.index(args.only) + 1] if args.only else MODULES
    receipt = {"all_listed_modules_compiled": args.only is None,
               "full_upper_bound_formalized": False, "compiler": version,
               "scope": "Partial formalization; not the BTnSS-to-BMS upper-bound theorem",
               "memory_mb": 2048, "threads": 1, "timeout_per_module": args.seconds,
               "compiler_executable_sha256": hashlib.sha256(Path(lean).read_bytes()).hexdigest(),
               "build_script_sha256_lf": hashlib.sha256(Path(__file__).read_text(encoding="utf-8").replace("\r\n", "\n").encode()).hexdigest(),
               "modules": [], "axiom_reports": []}
    for module in modules:
        source = ROOT / "src" / "BTnSSBMS" / f"{module}.lean"
        target = out / "BTnSSBMS" / f"{module}.olean"
        target.parent.mkdir(parents=True, exist_ok=True)
        content = source.read_text(encoding="utf-8")
        # A source check is additional to the kernel's printed dependencies.
        if re.search(r"\b(sorry|admit|axiom|native_decide|ofReduceBool)\b|\+native", content):
            raise SystemExit(f"Forbidden proof bypass in {source.name}")
        start = time.monotonic()
        # subprocess.run terminates and reaps its compiler on timeout. Lean
        # runs with one thread; no background helper processes are launched.
        result = subprocess.run([lean, "-M", "2048", "-j", "1", "--root=src",
                                 "-o", str(target), str(source.relative_to(ROOT))],
                                cwd=ROOT, env=env, text=True, encoding="utf-8",
                                capture_output=True, timeout=args.seconds)
        log = result.stdout + result.stderr
        (ROOT / ".build" / f"{module}.log").write_text(log, encoding="utf-8")
        print(f"{module}: exit={result.returncode}, {time.monotonic()-start:.2f}s", flush=True)
        if result.returncode:
            print(log)
            raise SystemExit(result.returncode)
        if source.read_text(encoding="utf-8") != content:
            raise SystemExit(f"Source changed during compilation: {source.name}")
        if "sorryAx" in log or "uses 'sorry'" in log:
            raise SystemExit(f"Invalid proof dependencies in {module}")
        for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
            found = {x.strip() for x in deps.split(",") if x.strip()}
            if not found <= {"propext", "Classical.choice", "Quot.sound"}:
                raise SystemExit(f"Unexpected axioms for {name}: {found}")
            receipt["axiom_reports"].append({"theorem": name, "axioms": sorted(found)})
        for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
            receipt["axiom_reports"].append({"theorem": name, "axioms": []})
        receipt["modules"].append({"module": f"BTnSSBMS.{module}",
            "sha256_lf": hashlib.sha256(content.replace("\r\n", "\n").encode()).hexdigest()})
    if args.only is None:
        audit = (ROOT / "src" / "BTnSSBMS" / "Audit.lean").read_text(encoding="utf-8")
        required = re.findall(r"^#print axioms (\S+)$", audit, re.MULTILINE)
        reported = [r["theorem"] for r in receipt["axiom_reports"]]
        if len(required) != len(set(required)) or sorted(required) != sorted(reported):
            raise SystemExit("Incomplete or duplicated axiom reports.")
    # Do not publish a receipt for sources edited while later modules compiled.
    for item in receipt["modules"]:
        source = ROOT / "src" / "BTnSSBMS" / (item["module"].rsplit(".", 1)[1] + ".lean")
        current = source.read_text(encoding="utf-8").replace("\r\n", "\n").encode()
        if hashlib.sha256(current).hexdigest() != item["sha256_lf"]:
            raise SystemExit(f"Source changed after compilation: {source.name}")
    current_build = Path(__file__).read_text(encoding="utf-8").replace("\r\n", "\n").encode()
    if hashlib.sha256(current_build).hexdigest() != receipt["build_script_sha256_lf"]:
        raise SystemExit("Build script changed during verification.")
    receipt["success"] = True
    serialized = json.dumps(receipt, ensure_ascii=False, indent=2) + "\n"
    (ROOT / ".build" / "verification.json").write_text(serialized, encoding="utf-8")
    if args.publish:
        if args.only or not receipt["axiom_reports"]:
            raise SystemExit("Publishing requires the full module list and axiom reports.")
        (ROOT / "VERIFICATION.json").write_text(serialized, encoding="utf-8")
        (ROOT / "verification").mkdir(exist_ok=True)
        shutil.copyfile(ROOT / ".build" / "Audit.log", ROOT / "verification" / "Audit.log")


if __name__ == "__main__":
    main()
