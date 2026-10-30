# Formal verification status

The full all-n even-cycle theorem is **not yet formalized**.

The following modules were accepted by Lean 4.35.0-rc2. Audited declarations
use only subsets of the standard axioms propext, Classical.choice and
Quot.sound. No sorryAx or project axioms occur in these accepted results.

| Module | Checked result |
|---|---|
| ArmBounds | U/N/P message bounds, EMPTY distinction, residues and unit-fuel reserve |
| Moves | Edge inclusion, additive inactive-pebble simulation, batches and triple burning |
| PathConstruction | Constructive path boundary attainment and exact-unit clearing |
| BalancedRoot | Balanced-root existence, endpoint pivot balance and opposite-triple bound |
| CaseBudgets | Arithmetic loss and fuel inequalities |
| Cycle | Actual graph definitions, next-vertex adjacency and threshold cardinality bound |
| CyclePaths | Cyclic arc chains, distinctness, coverage and mass identities |
| PathThreshold | Arbitrary configurations supported on a simple path above its threshold |
| UnitOperations | Funded unit pull/push as actual legal move sequences |

The central checked declarations are printed by [Audit.lean](Audit.lean).
Their accepted building blocks do not by themselves imply that every cycle
configuration is handled.

Remaining work:

1. Instantiate the operations in all antipodal-pile and endpoint-parity cases.
2. Connect their cleared arcs and mass budgets to the retained-path theorem.
3. Assemble the one-pivot argument, including n=2 and n=3.
4. Prove and audit the full cycle upper theorem and matching lower obstruction.

The original mathematical proof is recorded as fohn task #2, report #20.
The board still has separate review and final-synthesis gates; its part
counter is not a percentage of this Lean development.
