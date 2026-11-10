"""Validate the shared private dependency pin without invoking Lake or repository code."""

import json
import os
from pathlib import Path
import re
import tomllib


root = Path(os.environ.get("GITHUB_WORKSPACE", "."))
url = "https://github.com/plum-umd/plos-risc.git"
revisions = set()
for project in ("risc-lookup", "risc-handles", "risc-queue"):
    directory = root / "projects" / project
    configuration = tomllib.loads((directory / "lakefile.toml").read_text())
    manifest = json.loads((directory / "lake-manifest.json").read_text())
    requirements = [p for p in configuration["require"] if p["name"] == "plos"]
    packages = [p for p in manifest["packages"] if p["name"] == "plos"]
    if len(requirements) != 1 or len(packages) != 1:
        raise SystemExit(f"{project}: expected exactly one PL/OS dependency")
    requirement, package = requirements[0], packages[0]
    revision = package["rev"]
    if requirement["git"] != url or package["url"] != url:
        raise SystemExit(f"{project}: unexpected PL/OS repository URL")
    if requirement["rev"] != revision or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise SystemExit(f"{project}: configuration and manifest must pin the same full commit SHA")
    revisions.add(revision)

if len(revisions) != 1:
    raise SystemExit("The RISC projects must use the same PL/OS revision for the shared CI checkout")
print(f"revision={revisions.pop()}")
