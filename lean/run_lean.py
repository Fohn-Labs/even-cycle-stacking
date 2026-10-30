from pathlib import Path
import os
import json
import resource
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / "toolchain" / "lean-4.35.0-rc2-linux"
resource.setrlimit(resource.RLIMIT_AS, (12 * 1024**3, 12 * 1024**3))
allowed_cpus = sorted(os.sched_getaffinity(0))
os.sched_setaffinity(0, {allowed_cpus[os.getpid() % len(allowed_cpus)]})
os.chdir(ROOT)
env = {
    "PATH": f"{LEAN / 'bin'}:/usr/bin:/bin",
    "LEAN_NUM_THREADS": "1",
    "LEAN_IMPORT_WORKERS": "1",
    "CYCLESTACK_BUILD_LOCK": str(ROOT / "logs" / f"build-{os.getpid()}.lock"),
    "GIT_TERMINAL_PROMPT": "0",
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_CONFIG_GLOBAL": "/dev/null",
    "XDG_CACHE_HOME": str(ROOT / ".cache"),
}
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
search_paths = []
for package in manifest["packages"]:
    if package["type"] == "path":
        directory = ROOT / package["dir"]
    else:
        directory = ROOT / ".lake" / "packages" / package["name"]
    search_paths.append(str(directory / ".lake" / "build" / "lib" / "lean"))
search_paths.append(str(ROOT / ".lake" / "build" / "lib" / "lean"))
search_paths.append(str(LEAN / "lib" / "lean"))
env["LEAN_PATH"] = ":".join(search_paths)
args = sys.argv[1:]
if args[:3] == ["lake", "env", "lean"]:
    args = ["lean", *args[3:]]
if not args or args[0] not in {"lean", "lake", "leanchecker"}:
    raise SystemExit("Usage: python3 run_lean.py lean|lake|leanchecker [arguments]")
program = LEAN / "bin" / args[0]
child = subprocess.Popen([str(program), *args[1:]], env=env, start_new_session=True)
page_size = os.sysconf("SC_PAGE_SIZE")
memory_limit = 2_250_000_000
peak_rss = 0

def process_tree_rss(pid):
    pending, seen, total = [pid], set(), 0
    while pending:
        current = pending.pop()
        if current in seen:
            continue
        seen.add(current)
        try:
            values = Path(f"/proc/{current}/statm").read_text().split()
            total += int(values[1]) * page_size
            for task in Path(f"/proc/{current}/task").iterdir():
                try:
                    children = (task / "children").read_text()
                    pending.extend(int(value) for value in children.split())
                except FileNotFoundError:
                    pass
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total

try:
    while child.poll() is None:
        rss = process_tree_rss(child.pid)
        peak_rss = max(peak_rss, rss)
        if rss >= memory_limit:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
            print(f"Build stopped at RAM budget: {rss} bytes", file=sys.stderr)
            raise SystemExit(137)
        time.sleep(0.05)
except BaseException:
    if child.poll() is None:
        os.killpg(child.pid, signal.SIGKILL)
        child.wait()
    raise
print(f"Process-tree peak RSS: {peak_rss} bytes", file=sys.stderr)
raise SystemExit(child.returncode)
