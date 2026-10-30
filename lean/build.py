from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
wrapper = [sys.executable, str(ROOT / "run_lean.py"), "lean", "-j1"]

for name in ["Basic", "Transfer", "PebblingMove"]:
    output = ROOT / f"vendor/TreeStack/.lake/build/lib/lean/TreeStack/{name}.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        [*wrapper, "-R", "vendor/TreeStack", f"vendor/TreeStack/TreeStack/{name}.lean",
         "-o", str(output)], cwd=ROOT, check=True,
    )

modules = [
    "ArmBounds", "Moves", "PathConstruction", "BalancedRoot", "CaseBudgets",
    "Cycle", "CyclePaths", "PathThreshold", "UnitOperations",
]
for name in modules:
    path = ROOT / "CycleStack" / f"{name}.lean"
    if not path.exists():
        continue
    output = ROOT / ".lake/build/lib/lean/CycleStack" / f"{name}.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([*wrapper, str(path), "-o", str(output)], cwd=ROOT, check=True)

subprocess.run([*wrapper, "Audit.lean"], cwd=ROOT, check=True)
print("Checked the building blocks listed in Audit.lean.")
print("The full all-n cycle theorem is not yet formalized.")
