import Widgets.Sweep

/-!
# Widgets.FrozenLock — the frozen-lock exclusion and sweep termination

The iterated/potential half of the Zhao 2005 fast-sweeping structure, in
discrete min-plus form over `ℕ`:

* `sweep_unlocks` — **the frozen-lock exclusion**: if an edge `(a, b)` is in
  the never-retiring edge list and `d a + w a b < d b`, then one sweep lowers
  the head `b`.  A head frozen at a non-tight value while an improving edge
  is examined every sweep is structurally impossible.
* `Φ` — the machine potential `∑_v d v` (machinePotential shape):
  `Φ_run_le` every sweep is non-increasing in potential, `Φ_run_lt` every
  sweep that actually changes the machine strictly decreases it.
* `frozenLock_settles` — the run stabilizes within `Φ d₀ + 1` sweeps, and
  the stable state is exactly the tight fixpoint (`tight_of_stable`).

This is the no-carry consolidation seam: sweeps with no carry (all edges
re-examined every pass) must reach the Bellman fixpoint in at most
`Φ d₀ + 1` passes; the FT/SSSP consumer charges each *working* sweep
(`Φ_run_lt`) against the initial potential — amortized rows land as
`Φ_final ≤ Φ₀ − (number of working sweeps) · 1`.

Credit: H. Zhao, *A fast sweeping method for Eikonal equations*, Math.
Comp. 74 (2005) 603–627 (monotonicity, finite convergence); formalization
ours.
-/

namespace Widgets

variable {V : Type*} [DecidableEq V]

/-- Machine potential: the total distance mass. -/
noncomputable def Φ {V : Type*} [Fintype V] (w : V → V → ℕ) (E : List (V × V))
    (d : V → ℕ) : ℕ := ∑ v, d v

section FrozenLock

variable (w : V → V → ℕ) (E : List (V × V))

/-- **Frozen-lock exclusion**: an improving edge in the never-retiring list
unlocks its head in one sweep. -/
theorem sweep_unlocks (d : V → ℕ) (a b : V) (hab : (a, b) ∈ E)
    (himp : d a + w a b < d b) : sweep w E d b < d b :=
  lt_of_le_of_lt (sweep_hit w E d a b hab) himp

theorem Φ_sweep_le [Fintype V] (d : V → ℕ) : Φ w E (sweep w E d) ≤ Φ w E d :=
  Finset.sum_le_sum fun v _ => sweep_le w E d v

/-- Machine potential: the total distance mass (defined here so the section
variables apply cleanly). -/

theorem Φ_sweep_lt [Fintype V] (d : V → ℕ) (h : ∃ v, sweep w E d v < d v) :
    Φ w E (sweep w E d) < Φ w E d :=
  Finset.sum_lt_sum (fun u _ => sweep_le w E d u) h

/-- Every no-change sweep is a fixpoint sweep. -/
theorem exists_lt_of_ne_fix (d : V → ℕ) (hne : sweep w E d ≠ d) :
    ∃ v, sweep w E d v < d v := by
  by_contra hall
  push_neg at hall
  exact hne (funext fun v => le_antisymm (sweep_le w E d v) (hall v))

theorem frozenLock_terminates [Fintype V] :
    ∀ (N : ℕ) (d : V → ℕ), Φ w E d ≤ N →
    ∃ k ≤ N, sweepRun w E (k + 1) d = sweepRun w E k d := by
  intro N
  induction N with
  | zero =>
    intro d hd
    have h0 : ∀ v, d v = 0 := by
      intro v
      have h := Finset.sum_eq_zero_iff_of_nonneg (fun u _ => Nat.zero_le (d u)) |>.mp hd
        ⟨v, Finset.mem_univ v⟩
      exact h
    have hs : sweep w E d = d := by
      funext v
      have h1 : sweep w E d v ≤ d v := sweep_le w E d v
      rw [h0 v] at h1 ⊢
      exact Nat.le_zero.mp h1
    exact ⟨0, Nat.zero_le _, by rw [sweepRun_succ]; exact hs⟩
  | succ N ih =>
    intro d hd
    by_cases hs : sweep w E d = d
    · exact ⟨0, Nat.succ_le_succ Nat.zero_le _, by rw [sweepRun_succ]; exact hs⟩
    · obtain ⟨v, hv⟩ := exists_lt_of_ne_fix w E d hs
      obtain ⟨k, hk, hstab⟩ := ih (sweep w E d)
        (Nat.le_of_lt_succ (lt_of_lt_of_le (Φ_sweep_lt w E d ⟨v, hv⟩) hd))
      refine ⟨k + 1, by omega, ?_⟩
      calc sweepRun w E (k + 2) d
          = sweepRun w E (k + 1) (sweep w E d) := (sweepRun_sweep w E (k + 1) d).symm
        _ = sweepRun w E k (sweep w E d) := hstab
        _ = sweepRun w E (k + 1) d := sweepRun_sweep w E k d

theorem frozenLock_settles [Fintype V] (d : V → ℕ) :
    ∃ k ≤ Φ w E d, sweepRun w E (k + 1) d = sweepRun w E k d :=
  frozenLock_terminates w E (Φ w E d) d le_rfl

/-- Once stable, always stable: the suffix of a stationary run is stationary. -/
theorem stable_suffix {d : V → ℕ} {k : ℕ}
    (h : sweepRun w E (k + 1) d = sweepRun w E k d) :
    ∀ j, sweepRun w E (k + 1 + j) d = sweepRun w E (k + j) d := by
  intro j
  induction j with
  | zero => exact h
  | succ j ih =>
      have hidx : k + 1 + (j + 1) = (k + 1 + j) + 1 := by omega
      rw [hidx]
      exact congrArg (sweep w E) ih

/-- The run is stationary by potential + 1 sweeps. -/
theorem settled_by [Fintype V] (d : V → ℕ) :
    sweepRun w E (Φ w E d + 1) d = sweepRun w E (Φ w E d) d := by
  obtain ⟨k, hk, hstab⟩ := frozenLock_settles w E d
  have hsuf := stable_suffix (E := E) (w := w) hstab (Φ w E d - k)
  have h1 : k + 1 + (Φ w E d - k) = Φ w E d + 1 := by omega
  have h2 : k + (Φ w E d - k) = Φ w E d := by omega
  rwa [h1, h2] at hsuf

/-- The stable state satisfies every Bellman inequality on `E`. -/
theorem tight_of_stable (d : V → ℕ) (k : ℕ)
    (h : sweepRun w E (k + 1) d = sweepRun w E k d) (a b : V) (hab : (a, b) ∈ E) :
    sweepRun w E k d b ≤ sweepRun w E k d a + w a b :=
  (sweepFix_iff w E (sweepRun w E k d)).mp h a b hab

theorem Φ_run_le [Fintype V] (d : V → ℕ) : ∀ k, Φ w E (sweepRun w E k d) ≤ Φ w E d := by
  intro k
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact (Φ_sweep_le w E (sweepRun w E k d)).trans ih

/-- machinePotential shape: a working sweep strictly drops the potential
against the run's start. -/
theorem Φ_run_lt [Fintype V] (d : V → ℕ) (k : ℕ)
    (hne : sweepRun w E (k + 1) d ≠ sweepRun w E k d) :
    Φ w E (sweepRun w E (k + 1) d) < Φ w E d := by
  have h1 : Φ w E (sweepRun w E (k + 1) d) < Φ w E (sweepRun w E k d) := by
    rw [sweepRun_succ]
    refine Φ_sweep_lt w E (sweepRun w E k d) ?_
    by_contra hall
    push_neg at hall
    exact hne (funext fun v => le_antisymm (sweep_le w E (sweepRun w E k d) v) (hall v))
  exact lt_of_lt_of_le h1 (Φ_run_le w E d k)

end FrozenLock

end Widgets
