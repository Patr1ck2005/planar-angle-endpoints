"""Standard-library integrity check for an extracted source bundle, or a release zip."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

def verify(read, files):
    declared = json.loads(read("FILES.json"))
    assert set(files) == set(declared) | {"FILES.json"}, "missing or extra release files"
    for name, digest in declared.items():
        assert hashlib.sha256(read(name)).hexdigest() == digest, name
    index = json.loads(read("MODULES.json"))
    seen, external = set(), set()
    def visit(name):
        if name in seen:
            return
        seen.add(name)
        info = index["modules"][name]
        assert info["file"] == "src/" + name.replace(".", "/") + ".lean"
        assert declared[info["file"]] == info["sha256"], name
        for dep in info["imports"]:
            if dep in index["modules"]:
                visit(dep)
            else:
                external.add(dep)
    visit(index["root"])
    assert seen == set(index["modules"]) and external == set(index["external"])
    expected = {x["file"] for x in index["modules"].values()}
    assert expected == {f for f in files if f.startswith("src/")}
    assert len({p.casefold() for p in files}) == len(files)
    assert not any(f.endswith((".olean",".ilean",".exe")) for f in files)
    print(f"{len(seen)} project modules; {len(external)} direct external modules; {len(declared)} payload hashes verified.")

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("zip",nargs="?",type=Path)
    arg=parser.parse_args()
    if arg.zip:
        with zipfile.ZipFile(arg.zip) as z:
            names=z.namelist()
            assert len(set(names))==len(names)
            verify(z.read,names)
    else:
        root=Path(__file__).resolve().parent
        manifest=json.loads((root/"FILES.json").read_bytes())
        files=[*(str(p.relative_to(root).as_posix()) for p in (root/"src").rglob("*") if p.is_file()),
               *(f for f in manifest if not f.startswith("src/")),"FILES.json"]
        verify(lambda f:(root/f).read_bytes(),files)

