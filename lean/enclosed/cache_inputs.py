"""Optional: request only the archive's external module imports and their mathlib dependencies."""
import json
from pathlib import Path
import subprocess

package=Path(__file__).resolve().parent
inputs=sorted(s for s in json.loads((package/"MODULES.json").read_bytes())["external"] if s.startswith("Mathlib."))
raise SystemExit(subprocess.call(["lake","exe","cache","get",*inputs],cwd=package))

