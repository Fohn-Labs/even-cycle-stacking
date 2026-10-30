# Formal verification status

**The full even-cycle upper bound is accepted by Lean for every natural n >= 2.**

The headline declaration is CycleStack.even_cycle_stackable:

    forall n >= 2, forall C : Fin (2*n) -> Nat,
      mass C = 2^(n+1)-1 -> Stackable (evenCycle n) C

CycleStack.even_cycle_upper packages this as exact-mass universality.
C4_universal, C6_universal and C8_universal are direct specializations.
These are arbitrary-configuration statements with no ASH hypothesis and no
bound on n. Stackable means a finite legal move sequence ends with a positive
pile and zero pebbles at every other vertex.

A fresh build of all sixteen project modules and the final audit exited zero.
[Build output](results/build.log) and [deduplicated axiom output](results/audit.txt)
are included. The headline theorem uses only propext, Classical.choice and
Quot.sound. There is no sorryAx or project axiom in its dependencies.

## Scope

The matching lower bound is an existing theorem of Csernak and Soukup and
has a separate elementary derivation in the written notes. It is not yet
formalized in this project. The exact stacking-number equality combines
that known lower bound with the checked upper bound.

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

## Reproduce

    python3 bootstrap.py
    python3 run_lean.py lake exe cache get
    python3 build.py

The pinned dependencies and RAM guard are documented in README.md.
