# Formal verification status

**The exact even-cycle stacking number is accepted by Lean for every natural n >= 2.**

The headline declaration is CycleStack.even_cycle_stackingNumber:

    forall n >= 2,
      stackingNumber (evenCycle n) = 2^(n+1)-1

The function stackingNumber is the least exact size t >= 2 at which every
configuration stacks. The certificate establishes that this minimum exists,
proves universality at the displayed threshold, and rules out every smaller
admissible threshold. Both bounds are formalized in this project.

The unrestricted upper-bound declaration is CycleStack.even_cycle_stackable:

    forall n >= 2, forall C : Fin (2*n) -> Nat,
      mass C = 2^(n+1)-1 -> Stackable (evenCycle n) C

CycleStack.even_cycle_upper packages this as exact-mass universality.
C4_universal, C6_universal and C8_universal are direct specializations.
These are arbitrary-configuration statements with no ASH hypothesis and no
bound on n. Stackable means a finite legal move sequence ends with a positive
pile and zero pebbles at every other vertex.

A fresh build of all twenty-five project modules and the final audit exited zero.
The final fresh-kernel replay also exited zero.
[Build output](results/build.log) and [deduplicated axiom output](results/audit.txt)
are included. The equality theorem uses only propext, Classical.choice and
Quot.sound. There is no sorryAx or project axiom in its dependencies.
The final leanchecker invocation replays Exact and all of its imported
declarations into an empty kernel environment. This is a replay with Lean's
own kernel, not a claim of verification by a different kernel implementation.

## Scope

The matching lower bound is an existing theorem of Csernak and Soukup.
The formal witness places 2^(n+1)-3 pebbles at zero, one at the antipode,
and zero elsewhere. Its mass is 2^(n+1)-2.

The lower proof derives exact move-count balances and positive outward
counts for occupied arms that become empty. On a path these bound the two
arm fluxes at every possible final target. Their sum is nonpositive,
contradicting a positive stack. Folding the cycle to the path preserves
each actual legal move and transfers the obstruction back to the cycle.
No general tree-score necessity theorem or assumed lower-bound axiom is used.

Exact-size universality propagates upward on graphs without isolated
vertices. This converts the explicit obstruction into genuine minimality,
matching the source's least-t definition rather than an informal sharpness
statement alone. C4_exact, C6_exact and C8_exact give 7, 15 and 31.

Lean verification is distinct from human peer review, priority assessment,
and fohn's independent report-review workflow.

## Checked components

| Modules | Purpose |
|---|---|
| ArmBounds, UnitOperations | Quantitative arm bounds and funded unit clearing |
| Moves, PathConstruction, LocalClearing | Actual legal moves, inactive surplus and exact mass ledgers |
| BalancedRoot, CyclePaths, GoodRoot | Balanced root, cyclic geometry and at most one pivot |
| PathThreshold, CycleReduction | Arbitrary path stacking and retained-path endgame |
| SmallAntipode, EvenEnding, OddEnding | Complete cycle case split |
| CaseBudgets, Cycle, Upper | Arithmetic budgets, graph model and universal theorem |
| MoveCounts, PathFluxArithmetic, PathLower | Legal move ledgers and the endpoint lower obstruction |
| LowerConfig, GraphPushforward, CycleFold, Lower | Explicit cycle witness and lawful folding |
| StackingNumber, Exact | Least-threshold semantics and the exact formula |

## Reproduce

    python3 bootstrap.py
    python3 run_lean.py lake exe cache get
    python3 build.py

The build finishes by running the trust-level-zero statement/axiom audit
and leanchecker --fresh --verbose CycleStack.Exact, under the same RAM guard.

The pinned dependencies and RAM guard are documented in README.md.
