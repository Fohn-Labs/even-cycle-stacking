"""Replay compressed cycle certificates using only the pebbling move rule.

This module is independent of construct.py and has no tree or message functions.
"""

import argparse
import json
import sys
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integer(value):
    require(isinstance(value, str) and value and value.isascii() and value.isdigit(),
            "Expected nonnegative decimal string")
    return int(value)


def index(value, N):
    require(type(value) is int and 0 <= value < N, "Invalid vertex index")
    return value


def replay(certificate):
    require(certificate["format"] == "cycle-stack-batch-v1", "Unknown certificate format")
    n = certificate["n"]
    require(type(n) is int and n >= 2, "Invalid n")
    N, A = 2*n, 1 << n
    C = [integer(x) for x in certificate["initial"]]
    require(len(C) == N and sum(C) == 2*A-1, "Invalid initial configuration")
    initial_mass = sum(C)
    operations = certificate["operations"]
    p = certificate["prefix_batch_count"]
    require(type(p) is int and 0 <= p <= len(operations), "Invalid prefix length")
    moves = 0
    prefix_moves = None
    prefix_state = None
    if p == 0:
        prefix_moves, prefix_state = 0, list(C)
    burns, transfers = 0, 0
    for j, op in enumerate(operations, 1):
        u, v = index(op["u"], N), index(op["v"], N)
        k = integer(op["k"])
        require(k > 0 and (u-v) % N in (1, N-1), "Invalid edge or repetition count")
        if op["kind"] == "transfer":
            require(C[u] >= 2*k, "Transfer batch lacks pebbles")
            C[u] -= 2*k
            C[v] += k
            moves += k
            transfers += 1
        elif op["kind"] == "burn3":
            # k repetitions of u->v, u->v, v->u are legal under this guard.
            # Each repetition leaves v unchanged and removes three from u.
            require(C[u] >= 3*k+1, "Triple-burn batch lacks pebbles")
            C[u] -= 3*k
            moves += 3*k
            burns += 1
        else:
            raise ValueError("Unknown operation kind")
        if j == p:
            prefix_moves, prefix_state = moves, list(C)
    require(prefix_moves == integer(certificate["prefix_move_count"]), "Wrong prefix move count")
    require(prefix_state == [integer(x) for x in certificate["prefix_state"]], "Wrong prefix state")
    path = certificate["remaining_path"]
    require(len(set(path)) == len(path) and all(type(v) is int and 0 <= v < N for v in path),
            "Invalid remaining path vertices")
    require(all((u-v) % N in (1, N-1) for u, v in zip(path, path[1:])), "Nonedge in remaining path")
    if certificate["direct_initial_tree"]:
        require(p == 0 and len(path) == N, "Invalid direct-tree prefix")
    else:
        require(prefix_moves <= A and sum(prefix_state) >= A-1, "Prefix exceeds budget")
        path_set = set(path)
        require(len(path) == n and all(prefix_state[v] == 0 for v in range(N) if v not in path_set),
                "Support is not on the remaining n-vertex path")
    require(moves == integer(certificate["move_count"]), "Wrong total move count")
    require(C == [integer(x) for x in certificate["final"]], "Wrong final configuration")
    target = index(certificate["target"], N)
    require(C[target] > 0 and all(C[v] == 0 for v in range(N) if v != target), "Final state is not stacked")
    require(initial_mass-moves == sum(C), "Mass accounting failed")
    return {"n": n, "batches": len(operations), "transfer_batches": transfers,
            "burn3_batches": burns, "moves": str(moves), "target": target,
            "final_pile": str(C[target]), "prefix_moves": str(prefix_moves)}


def main():
    try:
        import resource
        resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
    except ImportError:
        pass
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    result = replay(json.loads(args.certificate.read_text()))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
