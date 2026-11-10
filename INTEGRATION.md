# INTEGRATION — which widget lands in which lane

One page. The consumers import from `Widgets.*`; module names are stable,
statement names above are the API. Pin is shared with `sssp-nlogn-lane`
(mathlib `d13f23b7…`, lean `v4.34.1`), so imports are drop-in.

## 1. FT `sssp-nlogn-lane` — `machinePotential` rows (`Submission/FibHeapRow.lean`)

**Import: `Widgets.FrozenLock` (+ engine `Widgets.Sweep`).**

- `row_nlog`'s potential argument (`machinePotential st + count·5 + …`) is
  exactly the `Φ_run_le` / `Φ_run_lt` shape: non-increasing per op, strict
  on working ops, charged against a start potential. The frozen-lock
  exclusion `sweep_unlocks` is the structural fact behind the
  **no-carry consolidation seam**: when every edge is re-examined each pass
  (no carry), a head cannot stay frozen at a non-tight value, so the
  consolidation walk terminates with `tight_of_stable` — the walk-length
  term the row charges at the `rankCap` log class.
- Concretely: instantiate `V` with the heap's node type, `E` with the
  never-retiring edge list of the consolidation frontier, `w` with the
  degree/edge charges. `Φ_run_lt` gives "working sweep ⟹ potential drop by
  ≥ 1"; the row's per-op `+5` constant composes on top.
- Named-seam note: `hmono` (the `kids`-degree monotonicity premise,
  Residual 1 in `ROW_STATEMENT.md`) is unrelated to these widgets — the
  widgets remove the *other* open premise (that sweeps with no carry
  terminate at the fixpoint).

## 2. `apsp-l1-work` — triangular product-round body + segment assembly (`machine/`, `STMTS.md`)

**Import: `Widgets.TriangularBatch`.**

- The product-round's bracket/triangular structure: each min-plus product
  round over an ordered candidate set is a triangular system
  (`Triangular`: candidate order = the stored edge order). `onePass_tight`
  is the license that **one batch pass settles the round** — replacing any
  iteration/re-sweep argument in `DenseRestartSelectionLoop`-style wrappers.
- The segmented assembly: adjacent segments compose because the seam edge
  list stays triangular across segment boundaries (concatenation of
  topologically ordered lists is topologically ordered); per-segment
  `onePass_tight` receipts concatenate.
- The `maskCleared`/`Post` machinery of `STMTS.md` consumes the license as:
  after the loop body's single sweep, every computed row satisfies its
  Bellman inequalities — the `Post` clause currently argued semantically.

## 3. `subset-sum-bridge` — BRIDGE ladder Bound-arithmetic (`BRIDGE.md`)

**Import: `Widgets.NetCalc`.**

- `mpConv_assoc` / `mpConv_comm`: the ladder's min-plus stage composition
  (service-curve-style chaining of per-stage bounds) needs associativity;
  Bound-arithmetic can now cite the named lemma instead of re-deriving.
- `serviceCurve_backlog`: any ladder stage that guarantees
  "output ≥ input ⊛ β" with stage arrival curve α gets the delay/backlog
  bound `≤ N` as a one-line corollary — the accounting N enters as the
  vertical-deviation bound `∀ v, α v ≤ β v + N`, which is the form our
  ℕ-cost tables already produce.
- `mpConv_self_le`: closure for arrival-curve-style step bounds.

## 4. Cross-lane discipline

- All statements ℕ-valued: `⊤`-free, `Nat` subtraction only through the
  truncated `-` in `mpConv` windows — imports compile without coercions.
- Every module compiles under `autoImplicit = false` (lane default).
- Axiom surface: standard three (`propext`, `Classical.choice`,
  `Quot.sound`), no `sorryAx`, no `native_decide` — receipts per landing in
  `receipts/`.
