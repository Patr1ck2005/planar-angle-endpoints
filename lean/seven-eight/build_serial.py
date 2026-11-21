"""Sequential cold build of the entire source closure using the pinned Lake environment."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import subprocess

root=Path(__file__).resolve().parent
index=json.loads((root/"MODULES.json").read_bytes())
out=root/".local-build"
out.mkdir(exist_ok=True)
def output(cmd):
    return subprocess.check_output(cmd,cwd=root,text=True,encoding="utf8").strip()
if sys.argv[1:] != ["--inside-lake"]:
    raise SystemExit(subprocess.call(["lake","env",sys.executable,str(Path(__file__).resolve()),"--inside-lake"],cwd=root))
lean=shutil.which("lean")
assert lean and "version 4.34.0," in output([lean,"--version"])
env=dict(os.environ,LEAN_PATH=str(out)+os.pathsep+os.environ["LEAN_PATH"])
done=set()
def build(mod):
    if mod in done:
        return
    row=index["modules"][mod]
    for d in row["imports"]:
        if d in index["modules"]:build(d)
    src=root/row["file"]
    assert hashlib.sha256(src.read_bytes()).hexdigest()==row["sha256"]
    obj=(out/Path(*mod.split("."))).with_suffix(".olean")
    obj.parent.mkdir(parents=True,exist_ok=True)
    flags=["-DautoImplicit=false"] if mod.startswith("Jsp000404.") else []
    print(mod,flush=True)
    subprocess.run([lean,"-j1","-R",root/"src",*flags,"-o",obj,src],cwd=root,env=env,check=True)
    done.add(mod)
build(index["root"])
subprocess.run([lean,root/"CheckPublic.lean"],cwd=root,env=env,check=True)
