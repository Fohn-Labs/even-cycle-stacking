# Compressed bigint stacking certificates

This portable Python standard-library artifact implements the balanced-root
construction for configurations of exactly `2^(n+1)-1` pebbles on `C_(2n)`,
`n >= 2`. It emits a compressed legal-move certificate instead of expanding
an exponential number of pebbling moves. A separate replayer verifies the
certificate using only the pebbling move rule, integer arithmetic, and cyclic
adjacency. The replayer does not import the constructor or use tree scores,
messages, arm lemmas, balanced roots, or pivot arguments.

The implementation is an executable companion to the candidate general proof.
Its tests exercise the implementation and the certificate format; they are
not a replacement for the proof. Any certificate accepted by the independent
replayer is a legal stacking certificate for that particular input regardless
of the proof status.

## Use

Python 3.8 or later, with no dependencies. Run from this directory:

```sh
python3 construct.py example_input.json my_certificate.json
python3 replay.py my_certificate.json
python3 test_artifact.py
```

`example_input.json` is the n=1000 empty-arm input on C2000. The constructor CLI
and replayer CLI have both been run successfully on it; their outputs are
saved as `example_certificate.json`, `cli_construct.json`, and `cli_replay.json`.

Input is either a JSON list of 2n pebble counts or an object containing that
list under `initial`. Counts can be nonnegative JSON integers or decimal
strings. Decimal strings are recommended for interchange. The constructor
checks that the input has exactly `2^(n+1)-1` pebbles. Vertices are indexed
0 through 2n-1 in cyclic order. Root selection is automatic; `--root INDEX`
can request a particular balanced root for diagnostic use.

All certificate pebble counts and repetition counts are decimal strings.
Vertex indices, n, and batch indices are ordinary JSON integers. The scripts
disable Python's decimal-digit conversion ceiling so it does not impose an
artificial limit on n. Both CLI scripts impose a 1 GiB address-space limit
when the Unix resource module is available. The code uses one execution
thread. The test driver additionally imposes a 180-second CPU limit.

## Certificate semantics

The format is `cycle-stack-batch-v1`. The `operations` list contains only two
operation kinds:

```json
{"kind":"transfer","u":0,"v":1,"k":"123456789"}
{"kind":"burn3","u":0,"v":1,"k":"123456789"}
```

For `transfer`, u and v must be adjacent and the source must contain at least
2k pebbles. This represents k consecutive moves u->v. The replayer subtracts
2k at u, adds k at v, and adds k to the expanded move count.

For `burn3`, u and v must be adjacent and the source must contain at least
3k+1 pebbles. It represents k repetitions of

```text
u -> v
u -> v
v -> u
```

Before repetition j (starting at zero), u has at least `3(k-j)+1 >= 4`
pebbles, so both outgoing moves are legal; their two arrivals allow the return
move. Each repetition decreases u by three and leaves v unchanged. Thus the
replayer subtracts 3k at u, leaves v unchanged, and adds 3k to the expanded
move count. This argument holds even if v already contains protected pebbles.

Neither script loops k times. All arithmetic uses Python arbitrary-precision
integers. The independent replayer checks every batch's guard, actual final
singleton support, the declared final configuration, total mass accounting,
and the saved cycle-prefix budget and remaining-path support. It rejects
unknown operation kinds. The certificate's route events are diagnostic data;
the legality check does not rely on them.

## Construction details

The tree transfer function is implemented directly, preserving `None` for an
EMPTY branch and integer zero for an occupied zero-message branch. Path
clearing uses an explicit action stack and precomputed suffix messages, so
large n does not depend on Python's recursion limit. A unit normalization of
arbitrarily large size emits one `burn3` batch. Finding a balanced root and
computing every score on the remaining path use sliding windows and two
linear scans. There is no search over individual pebble states or fuel values.

For a length-L push with internal mass M and T=2^L, choose the largest fuel
at most T-M in the required modulo-three class when M<=T-2. Otherwise choose
the unique fuel in {0,1,2} in that class. Weighted residues are computed modulo
three directly, so no large explicit weighted sum is needed. The final
certificate still checks actual batch funding at every step.

The number of emitted operations and arithmetic operations is linear in the
cycle length; the bit sizes of counts and JSON output also grow with n. Thus
compression removes dependence on the expanded move count, not the ordinary
cost of handling n-bit integers and writing them.

## Checks and saved examples

`test_artifact.py` constructs certificates, writes them as JSON, reads them
back, and sends the parsed objects to the independent replayer. All checks
passed. `test_results.json` and `test.log` record the run.

- 18 targeted families at each n in {10,20,50,100,500,1000}.
- Six small boundary examples, including the C4 donation case and the two
  C6 pivot cases with new antipode 0 or 1.
- Four automatic-root checks on rotated bigint inputs.
- Rejection checks for an underfunded transfer, an underfunded triple burn,
  and a corrupted total move count.

There are 118 successful construction/replay checks and 114 saved
certificates. Every algorithm route occurred, including a direct initial
tree, all b=0,1,2 base cases, b=3 donation, even endpoint reduction, both odd
endpoint reductions, and pivot reductions landing in multiple different
cases. Huge triple-burn repetitions occurred. The targeted families are
defined explicitly in `families()` in the test driver.

| n | Largest batch count among 18 families | Largest certificate, bytes |
|---:|---:|---:|
| 10 | 45 | 2,435 |
| 20 | 95 | 4,897 |
| 50 | 245 | 12,647 |
| 100 | 495 | 27,260 |
| 500 | 2,495 | 198,788 |
| 1000 | 4,995 | 553,663 |

For n=1000, `certificates/n1000_push_empty_arm.json` represents exactly
`2^1001-3` literal moves with 2,998 batches. The huge unit-normalization
example `n1000_pull_nonnegative_burn.json` has five batches, including a
single repeated triple burn. `n1000_pivot_low.json` demonstrates the pivot
followed by the odd low-triple case. The observed maximum resident-set size
of the test process was 24,120 KiB on this Linux run.

No external code, packages, state-space solver, logarithmic approximation,
floating-point pebble arithmetic, or literal move expansion is used.
