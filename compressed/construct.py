"""Construct compressed legal stacking certificates for even cycles.

Python standard library only. Integer pebble counts are serialized as decimal
strings so that JSON consumers need not support arbitrary-precision numbers.
"""

import argparse
import json
import sys
from pathlib import Path

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)


def limit_memory():
    try:
        import resource
    except ImportError:
        return
    resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))


def decimal(value):
    if isinstance(value, bool):
        raise ValueError("Boolean pebble count")
    if isinstance(value, int):
        result = value
    elif isinstance(value, str) and value and value.isascii() and value.isdigit():
        result = int(value)
    else:
        raise ValueError("Pebble counts must be nonnegative integers or decimal strings")
    if result < 0:
        raise ValueError("Negative pebble count")
    return result


def F(x):
    if x <= 1:
        return 2*x - 3
    return x//2 if x % 2 == 0 else (x-3)//2


def messages(values):
    """Suffix messages, preserving None for an empty suffix."""
    out = [None]*(len(values)+1)
    for i in range(len(values)-1, -1, -1):
        child = out[i+1]
        if child is not None or values[i]:
            out[i] = F(values[i] + (0 if child is None else child))
    return out


def message(values):
    return messages(values)[0]


def endpoint_stack(values, vertices, unit=False):
    """Stack at vertices[0], emitting O(length) algebraically checked batches.

    The explicit action stack replaces recursion, so long paths are supported.
    Every action mutates the virtual configuration and checks its batch guard.
    """
    data = list(values)
    initial_mass = sum(data)
    incoming = messages(data)
    out = []
    move_count = 0

    def transfer(i, j, k):
        nonlocal move_count
        assert k >= 0
        if not k:
            return
        assert data[i] >= 2*k, ("virtual batch funding", i, j, k, data[i])
        data[i] -= 2*k
        data[j] += k
        move_count += k
        out.append({"kind": "transfer", "u": vertices[i], "v": vertices[j], "k": str(k)})

    actions = [("clear", 1)] if len(data) > 1 else []
    while actions:
        action = actions.pop()
        kind, i = action[:2]
        if kind == "clear":
            if incoming[i] is None:
                continue
            child = incoming[i+1]
            x = data[i] + (0 if child is None else child)
            if x >= 2:
                actions.append(("finish_up", i, x))
            else:
                transfer(i-1, i, 2-x)
                actions.append(("finish_down", i))
            if child is not None:
                actions.append(("clear", i+1))
        elif kind == "finish_up":
            x = action[2]
            assert data[i] == x
            transfer(i, i-1, x//2)
            if x % 2:
                transfer(i-1, i, 1)
                transfer(i, i-1, 1)
        else:
            assert kind == "finish_down" and data[i] == 2
            transfer(i, i-1, 1)
    assert data[0] > 0 and all(x == 0 for x in data[1:])
    if unit:
        assert data[0] % 3 == 1
        k = (data[0]-1)//3
        if k:
            assert len(data) >= 2 and data[0] >= 3*k+1
            data[0] -= 3*k
            move_count += 3*k
            out.append({"kind": "burn3", "u": vertices[0], "v": vertices[1], "k": str(k)})
        assert data[0] == 1
    assert move_count == initial_mass - sum(data)
    return out


def balanced(c, order, A):
    n = len(c)//2
    a, b = c[order[0]], c[order[n]]
    q = sum(c[v] for v in order[1:n])
    r = sum(c[v] for v in order[n+1:])
    return a > b and q+b <= A-1 and r+b <= A-1


def find_balanced(c, A):
    """Linear sliding-window search; no dependence on pebble count."""
    N, n, total = len(c), len(c)//2, sum(c)
    q = sum(c[1:n])
    for root in range(N):
        a, b = c[root], c[(root+n) % N]
        r = total-a-b-q
        if a > b and q+b <= A-1 and r+b <= A-1:
            return root
        q += c[(root+n) % N] - c[(root+1) % N]
    raise AssertionError("No balanced root")


def path_scores(c, path):
    """All exact rooted-path scores in linear time."""
    left, right = [None]*len(path), [None]*len(path)
    m = None
    for i, v in enumerate(path):
        left[i] = m
        if m is not None or c[v]:
            m = F(c[v] + (0 if m is None else m))
    m = None
    for i in range(len(path)-1, -1, -1):
        v = path[i]
        right[i] = m
        if m is not None or c[v]:
            m = F(c[v] + (0 if m is None else m))
    return [c[v] + (0 if left[i] is None else left[i]) +
            (0 if right[i] is None else right[i]) for i, v in enumerate(path)]


def construct(initial, root=None):
    initial = [decimal(x) for x in initial]
    N = len(initial)
    if N < 4 or N % 2:
        raise ValueError("Expected an even cycle with at least four vertices")
    n, A = N//2, 1 << (N//2)
    if sum(initial) != 2*A-1:
        raise ValueError("Expected exactly 2^(n+1)-1 pebbles")
    if root is None:
        root = find_balanced(initial, A)
    if not isinstance(root, int) or isinstance(root, bool) or not 0 <= root < N:
        raise ValueError("Invalid root index")
    C = list(initial)
    operations, events = [], []
    move_count = 0

    def apply(op):
        nonlocal move_count
        u, v, k = op["u"], op["v"], int(op["k"])
        assert k > 0 and (u-v) % N in (1, N-1)
        if op["kind"] == "transfer":
            assert C[u] >= 2*k, ("actual batch funding", u, v, k, C[u])
            C[u] -= 2*k
            C[v] += k
            move_count += k
        else:
            assert op["kind"] == "burn3" and C[u] >= 3*k+1
            C[u] -= 3*k
            move_count += 3*k
        operations.append(op)

    def transfer(u, v, k=1):
        assert k >= 0
        if k:
            apply({"kind": "transfer", "u": u, "v": v, "k": str(k)})

    def apply_sequence(sequence):
        for op in sequence:
            apply(op)

    def pull(vertices):
        data = [C[v] for v in vertices[1:]]
        m = message(data)
        fuel = 1 if m is None else (1-m if m < 0 else (1-m) % 3)
        assert 0 <= fuel <= C[vertices[0]], ("pull funding", fuel, C[vertices[0]])
        apply_sequence(endpoint_stack([fuel]+data, vertices, unit=True))

    def push(vertices):
        L = len(vertices)-1
        data = [C[v] for v in vertices[1:-1]]
        mass, T = sum(data), 1 << L
        cap = T-mass if mass <= T-2 else 2
        weighted_residue = sum((2 if i % 2 else 1)*(x % 3)
                               for i, x in enumerate(data, 1)) % 3
        residue = (T-weighted_residue) % 3
        fuel = cap-(cap-residue) % 3
        assert 0 <= fuel <= C[vertices[0]], ("push funding", fuel, C[vertices[0]])
        virtual = [fuel]+data+[0]
        apply_sequence(endpoint_stack(list(reversed(virtual)), list(reversed(vertices)), unit=True))

    def clear_antipode(v, retained):
        b = C[v]
        assert b % 2 == 0 or b >= 5 or (b == 3 and C[retained] > 0)
        transfer(v, retained, b//2)
        if b % 2:
            transfer(retained, v)
            transfer(v, retained)
        assert C[v] == 0

    def reduce(order, pivots=0):
        assert pivots <= 1 and balanced(C, order, A)
        a, b, antipode = C[order[0]], C[order[n]], order[n]
        arms = [[order[0]]+order[1:n],
                [order[0]]+list(reversed(order[n+1:]))]
        q = [sum(C[v] for v in arm[1:]) for arm in arms]
        d = [C[arm[-1]] for arm in arms]
        M, B = [q[j]-d[j] for j in range(2)], A//2
        assert a+q[0] >= A and a+q[1] >= A
        if b == 0 and a == 1:
            path = order[n:]+order[:n]
            score = path_scores(C, path)[path.index(order[0])]
            assert score > 0
            events.append({"route": "b0_a1_initial_tree", "root": order[0]})
            return path, order[0], True, pivots
        if b == 0:
            events.append({"route": "b0_pull", "root": order[0]})
            chosen = 0
            pull(arms[0])
        elif b == 1:
            events.append({"route": "b1_push", "root": order[0]})
            chosen = 0
            push(arms[0]+[antipode])
            transfer(antipode, arms[1][-1])
        elif b == 2:
            events.append({"route": "b2_clear_pull", "root": order[0]})
            chosen = 0
            transfer(antipode, arms[1][-1])
            pull(arms[0])
        elif b == 3 and d == [0, 0]:
            events.append({"route": "b3_zero_donation", "root": order[0]})
            chosen = 0
            transfer(antipode, arms[0][-1])
            push(arms[0])
            transfer(arms[0][-1], antipode)
            transfer(antipode, arms[1][-1])
        else:
            even = [j for j in range(2) if d[j] % 2 == 0 and (b >= 4 or d[1-j] > 0)]
            if even:
                chosen = even[0]
                arm, retained = arms[chosen], arms[1-chosen][-1]
                events.append({"route": "even_last", "root": order[0], "chosen": chosen})
                transfer(arm[-1], arm[-2], C[arm[-1]]//2)
                pull(arm[:-1])
                clear_antipode(antipode, retained)
            else:
                assert all(x % 2 for x in d)
                high = [j for j in range(2) if M[j] >= B-2]
                K = b+d[0]+d[1]
                if high:
                    chosen, route = high[0], "odd_large_prefix"
                elif K <= A-1:
                    chosen = min(range(2), key=lambda j: d[j])
                    route = "odd_low_triple"
                else:
                    assert pivots == 0 and n >= 3
                    for j in (n-1, n+1):
                        assert balanced(C, order[j:]+order[:j], A)
                    new = order[n-1:]+order[:n-1]
                    newK = C[new[n]]+C[new[n-1]]+C[new[n+1]]
                    assert newK <= A-1 if n >= 4 else C[new[n]] <= 1
                    events.append({"route": "pivot", "oldroot": order[0],
                                   "newroot": new[0], "oldK": str(K), "newK": str(newK)})
                    return reduce(new, pivots+1)
                arm, retained = arms[chosen], arms[1-chosen][-1]
                events.append({"route": route, "root": order[0], "chosen": chosen})
                push(arm)
                assert C[arm[-1]] % 2 == 0
                transfer(arm[-1], antipode, C[arm[-1]]//2)
                clear_antipode(antipode, retained)
        assert C[antipode] == 0 and all(C[v] == 0 for v in arms[chosen][1:])
        assert move_count <= A and sum(C) >= A-1
        path = arms[1-chosen]
        path_set = set(path)
        assert all(C[v] == 0 for v in range(N) if v not in path_set)
        return path, None, False, pivots

    order = [(root+i) % N for i in range(N)]
    if not balanced(C, order, A):
        raise ValueError("The requested root is not balanced")
    path, target, direct, pivots = reduce(order)
    prefix_batches, prefix_moves = len(operations), move_count
    prefix_state = list(C)
    scores = path_scores(C, path)
    if target is None:
        j = max(range(len(path)), key=lambda j: scores[j])
        target = path[j]
    else:
        j = path.index(target)
    score = scores[j]
    assert score > 0
    branches = [list(reversed(path[:j])), path[j+1:]]
    occupied = []
    for arm in branches:
        m = message([C[v] for v in arm])
        if m is not None:
            occupied.append((m, arm))
    occupied.sort(key=lambda item: 0 if item[0] > 0 else (1 if item[0] == 0 else 2))
    for m, arm in occupied:
        apply_sequence(endpoint_stack([C[target]]+[C[v] for v in arm], [target]+arm))
    assert sum(x > 0 for x in C) == 1 and C[target] == score
    assert sum(initial)-move_count == sum(C)
    return {"format": "cycle-stack-batch-v1", "n": n,
            "initial": [str(x) for x in initial], "initial_root": root,
            "operations": operations, "move_count": str(move_count),
            "prefix_batch_count": prefix_batches, "prefix_move_count": str(prefix_moves),
            "prefix_state": [str(x) for x in prefix_state], "remaining_path": path,
            "direct_initial_tree": direct, "pivots": pivots, "events": events,
            "final": [str(x) for x in C], "target": target}


def main():
    limit_memory()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="JSON list, or object containing initial")
    parser.add_argument("output", type=Path, help="Compressed certificate JSON")
    parser.add_argument("--root", type=int, help="Use this balanced root instead of automatic selection")
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    initial = data["initial"] if isinstance(data, dict) else data
    certificate = construct(initial, args.root)
    args.output.write_text(json.dumps(certificate, separators=(",", ":"))+"\n")
    print(json.dumps({"n": certificate["n"], "batches": len(certificate["operations"]),
                      "moves": certificate["move_count"], "target": certificate["target"],
                      "output": str(args.output)}))


if __name__ == "__main__":
    main()
