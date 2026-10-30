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
    "LocalClearing", "CycleReduction", "GoodRoot", "SmallAntipode",
    "EvenEnding", "OddEnding", "Upper",
    "LowerConfig", "GraphPushforward", "MoveCounts", "PathFluxArithmetic",
    "PathLower", "CycleFold", "StackingNumber", "Lower", "Exact",
]
for name in modules:
    path = ROOT / "CycleStack" / f"{name}.lean"
    output = ROOT / ".lake/build/lib/lean/CycleStack" / f"{name}.olean"
    output.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run([*wrapper, str(path), "-o", str(output)], cwd=ROOT, check=True)

subprocess.run([*wrapper, "-t0", "Audit.lean"], cwd=ROOT, check=True)
subprocess.run(
    [sys.executable, str(ROOT / "run_lean.py"), "leanchecker", "--fresh",
     "--verbose", "CycleStack.Exact"], cwd=ROOT, check=True,
)
print("Kernel checked CycleStack.even_cycle_stackingNumber for every n >= 2.")
print("Both bounds and exact-threshold minimality are formalized.")
print("All imported declarations were replayed into a fresh kernel environment.")
