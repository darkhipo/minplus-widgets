# Receipts — minplus-widgets lane, first green landing

Date: 2026-11-09. Pin: mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
lean `v4.34.1` (shared with sssp-nlogn lane; mathlib package symlinked, no
fresh clone). Build discipline: detached `trap "" TERM`, `shlock`-guarded
(flock(1) absent on this host, R2125609507), live-pressure gated
(swap flat at ~9.7 GB/10.2 GB across 60 s samples before launch).

## Build receipts (three per landing)

1. **Exit code 0** — `lake build Widgets` → `Build completed successfully
   (769 jobs)` / `LAKE-EXIT:0`. Log: `build_final.log` (also `build_r2.log`
   predecessor in this dir).
2. **Named oleans** —
   `.lake/build/lib/lean/Widgets.olean`,
   `.lake/build/lib/lean/Widgets/{Sweep,TriangularBatch,FrozenLock,NetCalc}.olean`
   (sizes/timestamps in `build_final.log` tail).
3. **Axiom banners** (`#print axioms`, echoed in the build log):
   - `Widgets.Triangular.noSelfLoop` — no axioms
   - `Widgets.onePass_tight` — [propext, Classical.choice, Quot.sound]
   - `Widgets.sweep_unlocks` — [propext, Quot.sound]
   - `Widgets.tight_of_stable` — [propext, Quot.sound]
   - `Widgets.Φ_sweep_le`, `Φ_sweep_lt`, `frozenLock_settles`, `settled_by`,
     `Φ_run_le`, `Φ_run_lt` — [propext, Classical.choice, Quot.sound]
   - `Widgets.NetCalc.mpConv_comm`, `mpConv_assoc`, `mpConv_mono_right`,
     `mpConv_self_le`, `serviceCurve_backlog` — [propext, Classical.choice,
     Quot.sound]
   **No `sorryAx`, no `native_decide` anywhere.**

## Notes

- The first launch attempt died SIGKILLed (exit 137) mid-mathlib-rebuild
  because the module imported the `Mathlib.Tactic` barrel (not built in the
  shared checkout). Cure: minimal import sets that are fully built
  (`Logic.Function.Basic`, `Data.List.Basic`, `Order.Basic`,
  `Data.Fintype.Basic`, `Algebra.Order.BigOperators.Group.Finset`,
  `Data.Finset.Max`/`Image`, `Data.List.Range`) — zero mathlib rebuild work.
- All statements are ℕ-valued (no ℝ, no ⊤): directly importable into the
  ℕ-machine lanes.
- Named-premise seams: none (all primaries verified; see STATEMENTS.md).
