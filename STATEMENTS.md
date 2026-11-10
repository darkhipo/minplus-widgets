# STATEMENTS — minplus-widgets ledger

Lane: `darkhipo/minplus-widgets` (this directory). Pin: mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, toolchain `leanprover/lean4:v4.34.1`
— the same pin as the `sssp-nlogn` lane; the shared built mathlib is
symlinked from `../sssp-nlogn-lane/.lake/packages/` (no fresh clone; fleet
admission control, R2125609450).

Per-widget status, credit, and the exact statement shapes. All ℕ-valued:
`⊤` is never used; consumers in the ℕ-machine lanes import verbatim.

## Widget 1 — FrozenLock (`Widgets/FrozenLock.lean`, engine in `Widgets/Sweep.lean`)

**Credit: H. Zhao, "A fast sweeping method for Eikonal equations", Math.
Comp. 74 (2005) 603–627, DOI 10.1090/s0025-5718-04-01678-3** — verified
2026-11-09 via publisher + Scholars@Duke + OpenAlex records (monotonicity
and stability proven; convergence in finitely many sweeps, 2^n for distance
in n dims; mesh-size-independent). Formalization ours.

Source vocabulary → our mutation: Zhao's Gauss–Seidel sweeps with
alternating orderings over grid points → our never-retiring edge list `E`
relaxed in list order; "a value only decreases" → `sweep_le`;
"convergence in finitely many sweeps" → `frozenLock_settles` with the
ℕ-potential `Φ d = ∑_v d v`.

Key names:

- `Widgets.step`, `Widgets.sweep`, `Widgets.sweepRun` — the engine.
- `Widgets.sweep_le` — monotone non-increasing sweep (Zhao Thm 3.6 analog).
- `Widgets.sweep_hit` — an edge in the list drags its head to `≤ d a + w a b`.
- `Widgets.sweepFix_iff` — `sweep w E d = d ↔` all Bellman inequalities on `E`.
- `Widgets.sweep_untouched` — heads with no in-edges in the list never move.
- `Widgets.FrozenLock.sweep_unlocks` — **the frozen-lock exclusion**:
  `(a,b) ∈ E → d a + w a b < d b → sweep w E d b < d b`. A head frozen at a
  non-tight value while its improving edge is re-examined every sweep cannot
  persist.
- `Widgets.FrozenLock.Φ`, `Φ_sweep_le`, `Φ_run_le`, `Φ_run_lt` —
  machinePotential shape: `Φ` non-increasing per sweep, strictly decreasing
  on working sweeps, bounded by the start potential.
- `Widgets.FrozenLock.frozenLock_terminates` / `frozenLock_settles` /
  `settled_by` — stationarity within `Φ d₀ + 1` sweeps.
- `Widgets.FrozenLock.tight_of_stable` — the stable state is the Bellman
  fixpoint: the no-carry consolidation seam.

Status: **PROVED & BUILT** — `lake build Widgets` exit 0, olean minted,
axioms `[propext, Classical.choice, Quot.sound]` (receipts/RECEIPTS.md).

## Widget 2 — TriangularBatch (`Widgets/TriangularBatch.lean`)

**Credit: S. Luo, H. Zhao, "Convergence analysis of the fast sweeping
method for static convex Hamilton–Jacobi equations", Research in the
Mathematical Sciences 3:33 (2016), DOI 10.1186/s40687-016-0083-8** —
verified 2026-11-09 via Springer record (open access): convergence of FSM
on arbitrary meshes; *contraction property of monotone upwind schemes
combined with proper orderings*. The ordering mechanism is exactly what the
one-batch-pass license formalizes. Formalization ours.

Source vocabulary → our mutation: "proper orderings let one Gauss–Seidel
pass propagate information along the causality order" → our `Triangular`
edge list (`E.idxOf (x,y) < E.idxOf (y,z)` for in- before out-edges; cycles
and self-loops excluded by the condition itself) + `onePass_tight`.

Key names:

- `Widgets.Triangular` — `nodup` + `inBeforeOut` (the topological order).
- `Widgets.Triangular.noSelfLoop` — self-loops excluded by the order.
- `Widgets.TriangularBatch.onePass_tight` — **the batch-settle license**:
  one sweep along a triangular list leaves the state satisfying every
  Bellman inequality on the list:
  `(htri : Triangular E) → (a,b) ∈ E → sweep w E d₀ b ≤ sweep w E d₀ a + w a b`.

Status: **PROVED & BUILT** — exit 0, olean minted, axioms
`[propext, Quot.sound]` (receipts/RECEIPTS.md).

## Widget 3 — NetCalc (`Widgets/NetCalc.lean`)

**Credit: the min-plus network-calculus lineage — R. Cruz (1991);
C.-S. Chang, *Performance Guarantees in Communication Networks* (2000);
J.-Y. Le Boudec & P. Thiran, *Network Calculus*, LNCS 2050 (2001).**
Classical statements transcribed to discrete ℕ; proofs ours (in this
discrete form the delay bound is a one-page induction — see below).

Key names:

- `Widgets.NetCalc.mpConv` — `(α ⊛ β) t = min_{s ≤ t} (α s + β (t - s))`.
- `mpConv_le` / `le_mpConv` — the two characterization lemmas.
- `mpConv_comm`, **`mpConv_assoc`** — the min-plus algebra; associativity is
  THE structural named lemma (proof: both sides equal the min over the
  triple family `α u + β p + γ q`, `u + p + q = t`, via index pairing).
- `mpConv_mono_left` / `mpConv_mono_right` — monotonicity.
- `mpConv_self_le` — subadditive + `α 0 = 0` ⟹ `(α ⊛ α) ≤ α` (closure).
- `Widgets.NetCalc.serviceCurve_backlog` — **service curve ⇒ delay bound**:
  output `≥ f ⊛ β` (hsvc), input `≤ α` in leaky-bucket form (hfA), `N` a
  bound on the vertical deviation `∀ v, α v ≤ β v + N` (hN) ⟹
  `f t ≤ g t + N`.  (Discrete form; the `s = 0` convolution term carries
  `β t`, so no subadditivity premise is needed — noted honestly in the
  docstring.)

Status: **PROVED & BUILT** — exit 0, olean minted, axioms
`[propext, Quot.sound]` (receipts/RECEIPTS.md).

## Named-premise seams (D7 boundary)

None required. All three primaries were verified by publisher-level records
(AMS/Duke for Zhao 2005; Springer open-access for Luo–Zhao 2016; the
net-calc lineage is a book/monograph line, cited as lineage, statements
ours). If the build exposes a statement that cannot be discharged without a
paper-only fact, it will be re-landed here as an explicit named premise —
never a silent `sorry`.

## Receipts

Three per landing (lane convention): build exit 0, named `.olean` under
`.lake/build/lib/lean/Widgets/`, axiom banner (`#print axioms` →
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no
`native_decide`). Minted under `receipts/` at first green build; all builds
detached `trap "" TERM` under the fleet build lock.
