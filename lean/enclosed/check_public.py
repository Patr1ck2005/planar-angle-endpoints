"""Re-import the six public roots and compare their reported axioms with the archived receipt."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

root = Path(__file__).resolve().parent
if sys.argv[1:] != ["--inside-lake"]:
    raise SystemExit(subprocess.call(["lake", "env", sys.executable, str(Path(__file__).resolve()), "--inside-lake"], cwd=root))
env = os.environ.copy()
if (root / ".local-build").is_dir():
    env["LEAN_PATH"] = os.pathsep.join([str(root / ".local-build"), env.get("LEAN_PATH", "")])
lean = shutil.which("lean")
log = subprocess.run([lean, "-j1", "CheckPublic.lean"], cwd=root, env=env, capture_output=True, encoding="utf8")
text = log.stdout + log.stderr
print(text, end="")
if log.returncode or "warning:" in text or "sorryAx" in text:
    raise SystemExit("public import failed")
roots = json.loads((root / "evidence/PUBLIC-KERNEL.json").read_bytes())["roots"]
actual = dict(re.findall(r"^'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.M))
if set(actual) != set(roots) or len(roots) != 6:
    raise SystemExit("unexpected public axiom reports")
standard = {"propext", "Classical.choice", "Quot.sound"}
for name, printed in actual.items():
    if set(printed.split(", ")) != set(roots[name]) or set(roots[name]) != standard:
        raise SystemExit("unexpected axioms: " + name)
print("PASS: all six public roots imported with their three recorded standard axioms")
