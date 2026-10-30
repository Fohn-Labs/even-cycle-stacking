# Formalization of even-cycle stacking

Status: the full all-n even-cycle equality is kernel checked. Both bounds
and the least exact-size threshold are formalized. See STATUS.md and
CycleStack/Exact.lean; CycleStack/Upper.lean contains the unrestricted upper
bound separately.

The target is: for every natural n >= 2, every configuration of
2^(n+1)-1 pebbles on the undirected simple cycle with 2n vertices can be
transformed by legal pebbling moves into a positive configuration with support
exactly one. A matching explicit obstruction has mass one below that. The
lower proof uses actual move-count balances on the folded path, and
exact-size universality then supplies the least-threshold statement.

The mathematical argument is fohn task #2, verified report #20. Supplementary
reports #22, #23 and #24 record the exposition handoff, an initial-path
obstruction and elementary lower proof, and the primary-source comparison.
Those supplementary reports await independent checks.

The project uses TreeStack's existing definitions of configurations, legal
moves, reachability and stackability, and its integer transfer function.
TreeStack is an existing published dependency, not work authored in this
session. It is pinned to revision:

    4d4969703a9f0ca7a51cbe7edf0f0338cc95cafb

Source:
https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees

Its toolchain is Lean 4.35.0-rc2 and its Mathlib revision is:

    065356127b1dc0016f66b7283ce0ce2c4055aa55

All build commands must go through run_lean.py, which monitors the complete
build process tree and stops a run at 2.25 decimal GB of resident RAM. It
requests one worker thread and pins the process to one available CPU. At
most four project workers run at once, including the parent; their nine-GB
combined resident budget leaves headroom within the user's ten-GB limit.
Virtual address space is allowed to exceed resident memory because Lean's
startup reservation exceeds two GiB while its initial resident use is
under one hundred MB.

The accepted equality certificate compiles without sorryAx or project axioms.
Its final theorem assumes only n >= 2. The upper theorem separately takes
an arbitrary configuration at the exact initial mass. Audit.lean
prints the full statement, standard logical axioms, and underlying definitions
of moves, reachability, stackability, the cycle graph and the least stacking
number. A fresh complete build is recorded in results/build.log.

The default build ends with leanchecker --fresh CycleStack.Exact. This
replays the theorem and all imported declarations into an empty environment
using Lean's own kernel. The checker is bundled in the pinned toolchain and
runs through the same process-tree RAM guard.
