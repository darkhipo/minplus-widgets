# minplus-widgets — proved min-plus widgets for SSSP/APSP formalization (Lean 4)

## 1. What this is

Three proved, importable widget families for min-plus / shortest-path /
network-calculus formalization in Lean 4. All statements ℕ-valued (`⊤` never
used), proved, and built — statements *as proved*, with receipts; the exact
statement shapes and credit live in [STATEMENTS.md](STATEMENTS.md).

| Widget | Module | The one-line content | Proved from |
|---|---|---|---|
| **Sweep + FrozenLock** | `Widgets.Sweep`, `Widgets.FrozenLock` | The never-retiring edge-list sweep engine; monotone non-increasing (`sweep_le`); the **frozen-lock exclusion** `sweep_unlocks`; ℕ-potential `Φ` with strictly-decreasing working sweeps (`Φ_run_lt`) ⟹ stationarity within `Φ d₀ + 1` sweeps (`frozenLock_settles`); the stable state is the Bellman fixpoint (`tight_of_stable`) | Zhao 2005 |
| **TriangularBatch** | `Widgets.TriangularBatch` | The **batch-settle license** `onePass_tight`: one sweep along a triangular (topologically ordered, `Triangular`) edge list leaves every Bellman inequality on the list satisfied | Luo–Zhao 2016 |
| **NetCalc** | `Widgets.NetCalc` | Discrete min-plus convolution `mpConv` with the full algebra (`mpConv_comm`, **`mpConv_assoc`**, mono, `mpConv_self_le` closure) and **service curve ⟹ delay bound** `serviceCurve_backlog` | Cruz/Chang/Le Boudec–Thiran lineage |

Pin: Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
(`lakefile.toml`). Every module compiles with `autoImplicit = false`; axiom
surface is the standard three (`propext`, `Classical.choice`, `Quot.sound`) —
no `sorryAx`, no `native_decide`, per-module banners in
[receipts/RECEIPTS.md](receipts/RECEIPTS.md).

```lean
import Widgets.FrozenLock
import Widgets.TriangularBatch
import Widgets.NetCalc
```

## 2. Why it is up

An unpublished proof is indistinguishable from a claim. These lemmas are
already *consumed* — the integration map ([INTEGRATION.md](INTEGRATION.md))
shows which lane imports which widget:

- FT `sssp-nlogn`: `Φ_run_le`/`Φ_run_lt` + `sweep_unlocks`/`tight_of_stable`
  are the machinePotential shape and the no-carry consolidation seam behind
  `row_nlog`.
- `apsp-l1-work`: `onePass_tight` is the license that one batch pass settles a
  triangular product round.
- `subset-sum-bridge`: `mpConv_assoc`/`mpConv_comm` + `serviceCurve_backlog`
  carry the ladder's Bound-arithmetic stage composition.

Publishing makes that consumption checkable: a reader can diff the pin, build,
and see the same lemma names with the same axiom banners. The repo exists so
the widgets are reusable outside their lanes of origin and citable rather than
re-derivable.

## 3. What work can be done here

Each widget carries its named seams — statements this library makes it easy to
attack next:

- **FrozenLock**: the *no-carry consolidation seam* — `tight_of_stable` gives
  "stable = Bellman fixpoint"; porting the consolidation walk of the `sssp-nlogn`
  row onto it directly is open. The `Φ` machinery generalizes to any
  ℕ-potential; other potential-bounded termination arguments slot into
  `Φ_run_lt`'s shape.
- **TriangularBatch**: *segment assembly* — concatenations of triangular lists
  stay triangular, so per-segment `onePass_tight` receipts should concatenate;
  proving the concat lemma would license segmented batch passes over long
  ordered candidate sets.
- **NetCalc**: `serviceCurve_backlog` is stated for a single curve pair;
  the multi-stage cascade (chaining `mpConv` over a ladder) is a natural
  corollary-family. `mpConv_assoc` invites generalization from ℕ to any
  ordered commutative monoid with finset minima.
- **Porting candidates**: the widgets are ℕ-specialized by design (drop-in
  for ℕ-machine lanes). Generalizing `Sweep`/`FrozenLock` over a
  `CanonicallyOrderedCommSemiring`-style vertex-weight class would widen the
  audience; the edge-list engine itself is fixed and likely stays.

## 4. License and attribution

**License: [CFSF — the Copy-Free/Stays-Free License](https://github.com/darkhipo/cfsf)**
(canonical wording at that link; [LICENSE](LICENSE) here is byte-identical to
the canonical text). Use for any purpose; the one provision is that this work
itself stays free — nobody may fence it.

**Attribution — the mathematical content comes from these works; the Lean
formalizations are ours:**

- **H. Zhao**, *A fast sweeping method for Eikonal equations*, **Math. Comp.
  74 (2005) 603–627**, DOI [10.1090/s0025-5718-04-01678-3](https://doi.org/10.1090/s0025-5718-04-01678-3)
  → FrozenLock (`sweep_le` ≈ monotonicity/stability; `frozenLock_settles` ≈
  convergence in finitely many sweeps).
- **S. Luo, H. Zhao**, *Convergence analysis of the fast sweeping method for
  static convex Hamilton–Jacobi equations*, **Res. Math. Sci. 3:33 (2016)**,
  DOI [10.1186/s40687-016-0083-8](https://doi.org/10.1186/s40687-016-0083-8)
  (open access) → TriangularBatch (the proper-ordering mechanism behind
  `onePass_tight`).
- **R. Cruz** (1991); **C.-S. Chang**, *Performance Guarantees in Communication
  Networks* (2000); **J.-Y. Le Boudec, P. Thiran**, *Network Calculus*,
  **LNCS 2050 (2001)** → NetCalc (classical statements transcribed to discrete
  ℕ; the discrete proofs are ours).

Verification of the sources (publisher-level records) is recorded in
[STATEMENTS.md](STATEMENTS.md); no named premises were needed — all three
primaries stand on the standard axiom set.

### Mathlib-PR candidates

The sibling lemma-library placement analysis
([darkhipo/lemma-library, `docs/PLACEMENT.md`](https://github.com/darkhipo/lemma-library/blob/main/docs/PLACEMENT.md))
covers the campaign's Mathlib-candidacy methodology; it touched these min-plus
families only lightly, so here is the direct note without duplicating its
ranking machinery:

- **Likely candidates**: the `mpConv` algebra — `mpConv_comm`, `mpConv_assoc`,
  `mpConv_mono_left/right` — pure ℕ, finset-min arguments, no domain
  machinery. Mathlib has tropical-semiring infrastructure but, to our
  knowledge, no ℕ-sequence min-plus convolution; these would slot in as the
  discrete algebra layer. `mpConv_self_le` (closure under self-convolution) is
  a smaller sibling candidate.
- **Not candidates**: the `Sweep`/`FrozenLock` engine lemmas are welded to
  this repo's edge-list representation (never-retiring list, list-order
  relaxation) — generalizing the representation is a prerequisite for any
  upstreaming; `onePass_tight` is the same shape and might travel with a
  generalized `Triangular` predicate.

## Layout

```
Widgets.lean              umbrella import
Widgets/Sweep.lean        the sweep engine
Widgets/FrozenLock.lean   frozen-lock exclusion + Φ-termination
Widgets/TriangularBatch.lean  triangular order + onePass_tight
Widgets/NetCalc.lean      mpConv algebra + service curve ⟹ delay bound
STATEMENTS.md             statement ledger: credit, shapes, status
INTEGRATION.md            which lane consumes which widget
receipts/                 build logs + axiom banners
```

Build: `lake build Widgets` (fetches the pinned Mathlib on first run).
