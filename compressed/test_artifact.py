"""Branch-directed bigint interface checks; no external packages or code."""

import copy
import json
import resource
import time
from collections import Counter
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
resource.setrlimit(resource.RLIMIT_CPU, (180, 180))

from construct import construct
from replay import replay

base = Path(__file__).parent
certdir = base/"certificates"
certdir.mkdir(exist_ok=True)
rows, routes = [], Counter()


def check(name, c, expected, root=0):
    started = time.perf_counter()
    certificate = construct(c, root)
    data = json.dumps(certificate, separators=(",", ":"))+"\n"
    path = certdir/(name+".json")
    path.write_text(data)
    # Cross the actual JSON boundary, then call the independent replayer.
    result = replay(json.loads(path.read_text()))
    observed = [event["route"] for event in certificate["events"]]
    assert observed == expected, (name, expected, observed)
    routes.update(observed)
    row = {"name": name, "n": certificate["n"], "routes": observed,
           "batches": result["batches"], "burn3_batches": result["burn3_batches"],
           "moves": result["moves"], "move_bits": int(result["moves"]).bit_length(),
           "bytes": len(data.encode()), "seconds": time.perf_counter()-started,
           "file": str(path.relative_to(base))}
    rows.append(row)
    return certificate


small = [
    ("c4_direct", [1,3,0,3], ["b0_a1_initial_tree"]),
    ("c4_donation", [4,0,3,0], ["b3_zero_donation"]),
    ("c6_pivot_zero", [6,0,3,3,3,0], ["pivot","b0_pull"]),
    ("c6_pivot_one", [5,0,3,3,3,1], ["pivot","b1_push"]),
    ("c8_low_triple", [12,5,0,3,3,3,0,5], ["odd_low_triple"]),
    ("c8_pivot_large", [9,1,0,7,3,7,1,3], ["pivot","odd_large_prefix"]),
]
for name, c, expected in small:
    check(name, c, expected)


def vector(n, entries):
    c = [0]*(2*n)
    for v, count in entries.items():
        c[v] = count
    return c


def families(n):
    A, B, N = 1 << n, 1 << (n-1), 2*n
    yield "direct", vector(n, {0:1,n-1:A-1,n+1:A-1}), ["b0_a1_initial_tree"]
    yield "pull_negative", vector(n, {0:A,n-1:1,N-1:A-2}), ["b0_pull"]
    yield "pull_nonnegative_burn", vector(n, {0:2,1:A-2,N-1:A-1}), ["b0_pull"]
    yield "push_small_root", vector(n, {0:2,1:A-2,n:1,N-1:A-2}), ["b1_push"]
    yield "push_empty_arm", vector(n, {0:2*A-2,n:1}), ["b1_push"]
    yield "pair_then_pull", vector(n, {0:3,n-1:A-3,n:2,N-1:A-3}), ["b2_clear_pull"]
    yield "donation_dense", vector(n, {0:4,1:A-4,n:3,N-1:A-4}), ["b3_zero_donation"]
    yield "donation_empty", vector(n, {0:2*A-4,n:3}), ["b3_zero_donation"]
    yield "even_negative", vector(n, {0:2*A-8,n-1:2,n:4,n+1:1}), ["even_last"]
    yield "even_nonnegative", vector(n, {0:5,1:A-7,n-1:2,n:4,N-1:A-5}), ["even_last"]
    yield "even_b3_retained", vector(n, {0:4,1:A-4,n:3,n+1:1,N-1:A-5}), ["even_last"]
    yield "odd_large", vector(n, {0:3*B-4,1:B-2,n-1:1,n:3,n+1:1}), ["odd_large_prefix"]
    yield "odd_low", vector(n, {0:2*A-10,n-1:3,n:3,n+1:3}), ["odd_low_triple"]
    yield "pivot_zero", vector(n, {0:A-2,n-1:B-1,n:3,n+1:B-1}), ["pivot","b0_pull"]
    yield "pivot_one", vector(n, {0:A-3,n-1:B-1,n:3,n+1:B-1,N-1:1}), ["pivot","b1_push"]
    yield "pivot_two", vector(n, {0:A-4,n-1:B-1,n:3,n+1:B-1,N-1:2}), ["pivot","b2_clear_pull"]
    yield "pivot_large", vector(n, {0:A-7,1:1,n-1:B-1,n:3,n+1:B-1,N-2:1,N-1:3}), ["pivot","odd_large_prefix"]
    yield "pivot_low", vector(n, {0:B+3,n-1:A-5,n:3,n+1:3,N-3:B-9,N-2:1,N-1:3}), ["pivot","odd_low_triple"]


for n in (10,20,50,100,500,1000):
    for name, c, expected in families(n):
        certificate = check("n"+str(n)+"_"+name, c, expected)
        assert len(certificate["operations"]) <= 12*n+20
    print(json.dumps({"completed_n": n, "families": 18, "max_batches": max(row["batches"] for row in rows if row["n"] == n)}), flush=True)

# Automatic balanced-root selection, including rotated inputs, is a separate
# interface from the branch-directed root=0 checks above.
for n in (10,100,500,1000):
    c = next(item[1] for item in families(n) if item[0] == "pivot_low")
    c = c[7:]+c[:7]
    cert = construct(c)
    result = replay(json.loads(json.dumps(cert)))
    rows.append({"name":"automatic_rotated_n"+str(n),"n":n,
                 "routes":[e["route"] for e in cert["events"]],
                 "batches":result["batches"],"burn3_batches":result["burn3_batches"],
                 "moves":result["moves"],"move_bits":int(result["moves"]).bit_length()})

# Reject corrupted batches. These checks use the independent replayer and do
# not invoke any tree-score or arm-fuel computation.
source = json.loads((certdir/"n100_pull_nonnegative_burn.json").read_text())
corrupted = copy.deepcopy(source)
first = corrupted["operations"][0]
first["k"] = str(sum(int(x) for x in corrupted["initial"])+1)
try:
    replay(corrupted)
except ValueError:
    pass
else:
    raise AssertionError("Underfunded transfer accepted")
corrupted = copy.deepcopy(source)
for op in corrupted["operations"]:
    if op["kind"] == "burn3":
        op["k"] = str(sum(int(x) for x in corrupted["initial"])+1)
        break
else:
    raise AssertionError("Triple-burn branch not exercised")
try:
    replay(corrupted)
except ValueError:
    pass
else:
    raise AssertionError("Underfunded triple burn accepted")
corrupted = copy.deepcopy(source)
corrupted["move_count"] = str(int(corrupted["move_count"])+1)
try:
    replay(corrupted)
except ValueError:
    pass
else:
    raise AssertionError("Wrong total move count accepted")

result = {"checks": len(rows), "saved_certificates": len(list(certdir.glob("*.json"))),
          "routes": dict(routes), "rows": rows,
          "negative_replay_tests": ["underfunded transfer", "underfunded triple burn", "wrong move count"],
          "max_rss_kib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
          "notes": "Construction and replay use bigint batch operations; no literal move expansion and no search over fuel."}
(base/"test_results.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({key:value for key,value in result.items() if key != "rows"},sort_keys=True),flush=True)
