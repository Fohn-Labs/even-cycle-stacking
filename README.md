# Even-cycle stacking

A constructive candidate proof of

$$
\operatorname{stack}(C_{2n})=2^{n+1}-1,\qquad n\ge2,
$$

without the Almost Stacked Hypothesis, with reproducible move checkers and
a partial Lean formalization.

The mathematical argument is complete as written and recorded as verified
report #20 on **fohn task #2**. A separate Claude Opus 5.5 audit found no
substantive gap. This is an AI-assisted research draft; these checks do not
constitute human peer review or establish priority.

**The full cycle theorem has not yet been proved in Lean.** The checked
building blocks and remaining work are listed in [lean/STATUS.md](lean/STATUS.md).
The source-level proof, finite checks, and partial formalization have separate
roles; a successful finite run does not prove the arbitrary-n claim.

Start with:

- [Mathematical proof](proof/main.md).
- [Elementary lower-bound derivation and path-transfer obstruction](notes/path_transfer_and_lower_proof.md).
- [Primary-source comparison and credit](notes/prior_art.md).
- [Formalization status and exact theorem list](lean/STATUS.md).
- [Independent mathematical audit](reviews/claude_opus_55.md).

## Original papers and fohn

This work was coordinated on **fohn task #2**, with reports #20 and #22--#24.
The project organization is [Fohn Labs](https://github.com/Fohn-Labs).
Canonical fohn task/report page links will be added when the public URL is
available; the MCP connection supplies numeric IDs.

The original problem and known path/cycle lower bounds are due to
**Tamas Csernak and Lajos Soukup**:

- [Stacking and Clearing in Graph Pebbling, arXiv:2604.22341v1](https://arxiv.org/abs/2604.22341v1).
- [The Almost Stacked Hypothesis: A Conjectural Analogue of Sjostrand's Cover Pebbling Theorem, arXiv:2610.09650v1](https://arxiv.org/abs/2610.09650v1).

The exact branch transfer function, EMPTY distinction, and tree stackability
criterion are existing work by **John Fairfax-Ball**:

- [The stacking number of a tree, arXiv:2609.31811v2](https://arxiv.org/abs/2609.31811v2).
- [TreeStack formal source](https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees), pinned to revision 4d4969703a9f0ca7a51cbe7edf0f0338cc95cafb.
- [Related random-path message results, arXiv:2609.39633v1](https://arxiv.org/abs/2609.39633v1).

The finite values for C6 and C8 were already reported in the
[authors' pebbling repository](https://github.com/lajossoukup/pebbling).
No discovery or priority claim is made for those values.

## Reproduce the finite checks

Requires Python 3 and a C++17 compiler on Linux:

    python3 verify/run_cycle_verifier.py 2 1
    python3 verify/run_cycle_verifier.py 3 1
    python3 verify/run_cycle_verifier.py 4 8
    python3 verify/run_cycle_verifier.py 10 8 10000

Arguments are n, worker count, and optional sample count. Omit the final
argument for exhaustive enumeration. The checker constructs a sequence and
replays every move, checking adjacency, source fuel, mass loss and final
support. It imposes a two-GiB address-space limit and CPU-time limit.

Recorded runs:

| Cycle | Configurations | Individually checked legal moves |
|---|---:|---:|
| C4 | 120, exhaustive | 440 |
| C6 | 15,504, exhaustive | 146,814 |
| C8 | 12,620,256, exhaustive | 254,809,131 |

Saved logs are in [verify/logs](verify/logs). Samples through C20 also passed.
These are implementation checks; the all-n conclusion rests on the proof.

For compact certificates whose move counts are exponentially large, see
[compressed](compressed/README.md) and the [algorithmic note](proof/compact_certificates.md).

## Reproduce the checked Lean building blocks

See [lean/README.md](lean/README.md) and [lean/STATUS.md](lean/STATUS.md).
The pinned environment uses Lean 4.35.0-rc2 and Mathlib revision
065356127b1dc0016f66b7283ce0ce2c4055aa55.

On x86-64 Linux, with Python 3.12+, git, tar, zstd and flock:

    cd lean
    python3 bootstrap.py
    python3 run_lean.py lake exe cache get
    python3 build.py

The build wrapper monitors each complete process tree and stops it at
2.25 decimal GB of resident RAM. At most four project workers are used,
leaving headroom below the research session's ten-GB total limit.
Kernel acceptance and axiom audits apply only to the declarations listed
in the formalization status file, not to the unfinished cycle theorem.

## Provenance

Developed in a Codex research session directed by the repository owner, with
parallel mathematical and Lean workers. The local independent review used
Claude Opus 5.5 and a separate implementation. Source credits and the
distinction between board review, computation and kernel checking are
preserved in the notes.

Original repository files are available under the MIT license. Downloaded
dependencies retain their own licenses; see [THIRD_PARTY.md](THIRD_PARTY.md).
