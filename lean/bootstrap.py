from pathlib import Path
import hashlib
import json
import re
import resource
import shlex
import subprocess
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
LEAN = ROOT / "toolchain" / "lean-4.35.0-rc2-linux"
(ROOT / "toolchain").mkdir(exist_ok=True)
(ROOT / "vendor").mkdir(exist_ok=True)
(ROOT / "logs").mkdir(exist_ok=True)

def download(url, path, expected):
    if not path.exists():
        print(f"Downloading {path.name}", flush=True)
        with urllib.request.urlopen(url, timeout=120) as source, path.open("wb") as dest:
            while block := source.read(1024 * 1024):
                dest.write(block)
    with path.open("rb") as stream:
        actual = hashlib.file_digest(stream, "sha256").hexdigest()
    if actual != expected:
        raise RuntimeError(f"Checksum mismatch for {path.name}: {actual}")

if not LEAN.exists():
    download(
        "https://github.com/leanprover/lean4/releases/download/v4.35.0-rc2/"
        "lean-4.35.0-rc2-linux.tar.zst",
        ROOT / "toolchain/lean-4.35.0-rc2-linux.tar.zst",
        "b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049",
    )
    subprocess.run(
        ["tar", "--extract", "--use-compress-program=unzstd", "--file",
         str(ROOT / "toolchain" / "lean-4.35.0-rc2-linux.tar.zst"),
         "--directory", str(ROOT / "toolchain")],
        check=True,
    )
tree_root = ROOT / "vendor/TreeStack"
if not tree_root.exists():
    archive = ROOT / "vendor/treestack-source.tar.gz"
    revision = "4d4969703a9f0ca7a51cbe7edf0f0338cc95cafb"
    download(
        "https://github.com/jfairfaxball-348/"
        "TreeStack-Structural-Certificates-for-Stacking-on-Trees/archive/"
        + revision + ".tar.gz",
        archive,
        "cbb9c62b2bf19e65b868d18b3bfd4fedf054db7e976bdab8dcb3112e45157486",
    )
    with tarfile.open(archive) as source:
        source.extractall(ROOT / "vendor", filter="data")
    (ROOT / "vendor" /
     ("TreeStack-Structural-Certificates-for-Stacking-on-Trees-" + revision)).rename(tree_root)

# Only import lists are trimmed; upstream definitions and theorem bodies remain intact.
for name, imports in {
    "Transfer.lean": "import Mathlib.Tactic.NormNum\nimport Lean.Elab.Tactic.Omega\n",
    "PebblingMove.lean": "import Mathlib.Tactic.Push\nimport Lean.Elab.Tactic.Omega\n",
}.items():
    path = tree_root / "TreeStack" / name
    source = path.read_text()
    if source.startswith("import Mathlib\n"):
        path.write_text(imports + source[len("import Mathlib\n"):])
    elif not source.startswith(imports):
        raise RuntimeError(f"Unexpected upstream imports in {name}")

raw_lean = LEAN / "bin/lean-raw"
if not raw_lean.exists():
    (LEAN / "bin/lean").rename(raw_lean)
raw_command = shlex.quote(str(raw_lean))
launcher = (
    "#!/bin/sh\n"
    'for arg in "$@"; do\n'
    ' case "$arg" in\n'
    "  --print-prefix|--version|--help|-h) exec " + raw_command + ' -j1 "$@" ;;\n'
    " esac\n"
    "done\n"
    'if [ -z "$CYCLESTACK_BUILD_LOCK" ]; then\n'
    " exec " + raw_command + ' -j1 "$@"\n'
    "fi\n"
    'exec /usr/bin/flock "$CYCLESTACK_BUILD_LOCK" ' + raw_command + ' -j1 "$@"\n'
)
(LEAN / "bin/lean").write_text(launcher)
(LEAN / "bin/lean").chmod(0o755)
env = {
    "PATH": f"{LEAN / 'bin'}:/usr/bin:/bin",
    "LEAN_NUM_THREADS": "1",
    "GIT_TERMINAL_PROMPT": "0",
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_CONFIG_GLOBAL": "/dev/null",
}
manifest = json.loads((ROOT / "vendor/TreeStack/lake-manifest.json").read_text())
for package in manifest["packages"]:
    name, url, rev = package["name"], package["url"], package["rev"]
    if not re.fullmatch(r"[A-Za-z0-9_-]+", name):
        raise ValueError("Invalid dependency name")
    if not url.startswith(("https://github.com/leanprover-community/",
                           "https://github.com/leanprover/")):
        raise ValueError("Unexpected dependency host")
    if not re.fullmatch(r"[0-9a-f]{40}", rev):
        raise ValueError("Unpinned dependency")
    dest = ROOT / ".lake" / "packages" / name
    dest.mkdir(parents=True, exist_ok=True)
    if not (dest / ".git").exists():
        subprocess.run(["git", "init", "--quiet", str(dest)], env=env, check=True)
        subprocess.run(["git", "-C", str(dest), "remote", "add", "origin", url],
                       env=env, check=True)
    got = subprocess.run(["git", "-C", str(dest), "rev-parse", "HEAD"],
                         env=env, capture_output=True, text=True)
    if got.returncode == 0 and got.stdout.strip() == rev:
        print(f"{name}: pinned revision already present", flush=True)
        continue
    print(f"{name}: fetching pinned revision", flush=True)
    subprocess.run(["git", "-c", "pack.threads=1", "-C", str(dest),
                    "fetch", "--quiet", "--depth", "1", "origin", rev],
                   env=env, check=True)
    subprocess.run(["git", "-C", str(dest), "checkout", "--quiet",
                    "--detach", rev], env=env, check=True)
print("Pinned dependency sources are ready.", flush=True)
