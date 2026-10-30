<div align="center">

<h1>Even-cycle stacking</h1>

<p>A constructive proof with a Lean-checked exact formula</p>

<h3>stack(C<sub>2n</sub>) = 2<sup>n+1</sup> − 1 &nbsp; for every n ≥ 2</h3>

<p>
<a href="proof/main.md"><strong>Read the proof</strong></a> &nbsp;·&nbsp;
<a href="lean/CycleStack/Exact.lean">Lean theorem</a> &nbsp;·&nbsp;
<a href="lean/STATUS.md">Verification status</a> &nbsp;·&nbsp;
<a href="https://arxiv.org/abs/2604.22341v1">Original paper</a> &nbsp;·&nbsp;
<a href="https://github.com/Fohn-Labs">fohn</a>
</p>

</div>

A pebbling move removes two pebbles from one vertex and places one on a
neighbour. A configuration is stackable when all surviving pebbles can be
brought to a single vertex.

This project gives a constructive argument for the exact stacking number
of every even cycle, without the Almost Stacked Hypothesis.

| Result | Evidence |
|:--|:--|
| Exact least stacking number, for every n ≥ 2 | **Lean checked** — [equality theorem](lean/CycleStack/Exact.lean) |
| Every configuration at the target mass stacks, for all n ≥ 2 | **Lean checked** — [full upper-bound theorem](lean/CycleStack/Upper.lean) |
| Matching obstruction one pebble below the threshold | **Lean checked** — [lower-bound theorem](lean/CycleStack/Lower.lean), formalizing the known obstruction from the [original paper](https://arxiv.org/abs/2604.22341v1) |
| Legal move sequences on C4, C6 and C8 | **Exhaustively replayed** — [saved results](verify/logs) |
| Independent mathematical audit | **Supported** — [Claude Opus 5.5 review](reviews/claude_opus_55.md) |

The Lean certificate proves **both bounds and the least-threshold equality**.
Its only mathematical premise is n ≥ 2. The final check replays the declarations
and their imports into a fresh Lean kernel environment.
See the [exact scope and axiom audit](lean/STATUS.md).

## Explore the argument

The proof selects a balanced root, clears one side of the cycle within a
mass budget, and finishes on a path. A single pivot handles the remaining
large-triple case.

| Start here | Contents |
|:--|:--|
| [Main proof](proof/main.md) | Complete argument, including all small-cycle and parity cases |
| [Lean source](lean/CycleStack) | Legal moves, arm bounds, root selection and the all-n theorem |
| [Axiom audit](lean/results/audit.txt) | Dependencies of the checked declarations |
| [Path obstruction and lower bound](notes/path_transfer_and_lower_proof.md) | Why an initial spanning path can fail, and a direct lower-bound proof |
| [Compact certificates](compressed/README.md) | Large-n examples without expanding exponentially many moves |
| [Prior-work comparison](notes/prior_art.md) | Exact source statements, method overlap and search limits |
| [Paper handoff](notes/pdf_handoff.md) | Required proof contents, formal declarations and review status |

## Reproduce

**Move-by-move verification** requires Python 3 and a C++17 compiler:

    python3 verify/run_cycle_verifier.py 2 1
    python3 verify/run_cycle_verifier.py 3 1
    python3 verify/run_cycle_verifier.py 4 8

The arguments are n and worker count. Add a final sample count for a sampled
run. Each move is checked for adjacency, available fuel and the resulting
configuration.

| Cycle | Configurations | Legal moves checked |
|:--|--:|--:|
| C4 | 120 | 440 |
| C6 | 15,504 | 146,814 |
| C8 | 12,620,256 | 254,809,131 |

These finite checks support the implementation. The all-n proof is symbolic.

**Lean verification** uses pinned Lean and Mathlib versions. On x86-64 Linux
with Python 3.12+, git, tar, zstd and flock:

    cd lean
    python3 bootstrap.py
    python3 run_lean.py lake exe cache get
    python3 build.py

The runner monitors the full build process tree. Four workers are limited
to a combined nine GB of resident RAM, leaving headroom under the session's
ten-GB budget. Details are in [lean/README.md](lean/README.md).

## Sources and credit

The problem, path theorem and even-cycle lower bound are due to
**Tamás Csernák and Lajos Soukup**:

- [Stacking and Clearing in Graph Pebbling](https://arxiv.org/abs/2604.22341v1).
- [The Almost Stacked Hypothesis](https://arxiv.org/abs/2610.09650v1).
- [Original computational data](https://github.com/lajossoukup/pebbling), which already reports the finite C6 and C8 values.

The transfer function, EMPTY distinction and exact tree criterion are
existing work by **John Fairfax-Ball**:

- [The stacking number of a tree](https://arxiv.org/abs/2609.31811v2) and its [TreeStack formalization](https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees).
- [Related random-path message results](https://arxiv.org/abs/2609.39633v1).

Developed through **[fohn](https://github.com/Fohn-Labs), task #2**.
The written argument is recorded as verified report #20; reports #22--#24
contain companion results and source notes. Board verification, Lean
checking and human peer review are distinct.

This is AI-assisted research directed by the repository owner. No literature
priority or human peer-review claim is made. Original files use the
[MIT license](LICENSE); dependencies retain their [own licenses](THIRD_PARTY.md).
