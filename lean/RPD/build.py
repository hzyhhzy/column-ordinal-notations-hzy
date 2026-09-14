#!/usr/bin/env python3
"""Independent bounded build of this exact source-closed Lean project."""
from pathlib import Path
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verification_core import entry

if __name__ == "__main__":
    raise SystemExit(entry(Path(__file__).resolve().parent))
