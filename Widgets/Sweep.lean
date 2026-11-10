import Mathlib.Tactic

/-!
# Widgets.Sweep — the discrete min-plus relaxation engine

The tropical sweep: a fixed, never-retiring edge list `E : List (V × V)` is
relaxed by Gauss-Seidel `min`-updates

    d b := min (d b) (d a + w a b)     for each edge (a, b) in list order.

This is the discrete min-plus shadow of the fast-sweeping method:

* values only ever decrease (Zhao 2005, monotonicity of the sweep);
* an improving edge forces its head down *within one sweep* — a "frozen
  lock" on a head cannot persist while its edge stays in the list;
* the fixpoint of the sweep is exactly the Bellman (tightness) system
  `d b ≤ d a + w a b` on `E`.

Credit: H. Zhao, *A fast sweeping method for Eikonal equations*, Math.
Comp. 74 (2005) 603–627 (monotonicity, finite convergence); formalization
ours, in ℕ so it imports verbatim into the ℕ-valued machine lanes.
-/

namespace Widgets

variable {V : Type*} [DecidableEq V]

/-- One min-plus relaxation of the edge `e = (a, b)` against `d`:
the head's value drops to `min (d b) (d a + w a b)`. -/
def step (w : V → V → ℕ) (d : V → ℕ) (e : V × V) : V → ℕ :=
  Function.update d e.2 (min (d e.2) (d e.1 + w e.1 e.2))

/-- The sweep: relax the edges of `E` in list order (Gauss-Seidel). -/
def sweep (w : V → V → ℕ) : List (V × V) → (V → ℕ) → (V → ℕ)
  | [], d => d
  | e :: E, d => sweep w E (step w d e)

theorem step_le (w : V → V → ℕ) (d : V → ℕ) (e : V × V) (v : V) :
    step w d e v ≤ d v := by
  unfold step
  rw [Function.update_apply]
  by_cases h : e.2 = v
  · rw [if_pos h, h]
    exact min_le_left _ _
  · rw [if_neg h]
    exact le_rfl

theorem sweep_le (w : V → V → ℕ) (E : List (V × V)) (d : V → ℕ) (v : V) :
    sweep w E d v ≤ d v := by
  induction E generalizing d with
  | nil => rfl
  | cons e E ih => exact (ih (step w d e) v).trans (step_le w d e v)

/-- Every value at `v` survives a sweep that never relaxes an edge into `v`. -/
theorem sweep_untouched (w : V → V → ℕ) : ∀ (E : List (V × V)) (d : V → ℕ) (v : V),
    (∀ z : V, (z, v) ∉ E) → sweep w E d v = d v := by
  intro E
  induction E with
  | nil => intro d v _; rfl
  | cons e E ih =>
    intro d v hf
    obtain ⟨x, y⟩ := e
    by_cases hy : y = v
    · exact absurd (List.mem_cons.mpr (Or.inl (by rw [Prod.mk.injEq]; exact ⟨rfl, hy⟩)))
        (hf x)
    · show sweep w E (step w d (x, y)) v = d v
      rw [ih (step w d (x, y)) v (fun z hz =>
        hf z (List.mem_cons_of_mem _ hz))]
      unfold step
      rw [Function.update_apply, if_neg hy]

/-- An improving edge in the list forces the sweep to lower the head at least
to `d a + w a b` — the frozen-lock exclusion at the single-edge level. -/
theorem sweep_hit (w : V → V → ℕ) : ∀ (E : List (V × V)) (d : V → ℕ) (a b : V),
    (a, b) ∈ E → sweep w E d b ≤ d a + w a b := by
  intro E
  induction E with
  | nil => intro d a b h; cases h
  | cons e E ih =>
    intro d a b h
    obtain ⟨x, y⟩ := e
    show sweep w E (step w d (x, y)) b ≤ d a + w a b
    by_cases he : (x, y) = (a, b)
    · subst he
      refine (sweep_le w E (step w d (a, b)) b).trans ?_
      unfold step
      rw [Function.update_apply, if_pos rfl]
      exact min_le_right _ _
    · refine (ih (step w d (x, y)) a b h).trans ?_
      exact step_le w d (x, y) a

/-- A sweep fixes `d` iff `d` is tight (satisfies all Bellman inequalities on
`E`).  Forward direction: Zhao 2005's fixpoint characterization. -/
theorem tight_of_fixpoint (w : V → V → ℕ) : ∀ (E : List (V × V)) (d : V → ℕ),
    sweep w E d = d → ∀ (a b : V), (a, b) ∈ E → d b ≤ d a + w a b := by
  intro E
  induction E with
  | nil => intro d _ a b hb; cases hb
  | cons e E ih =>
    intro d hfix a b hab
    obtain ⟨x, y⟩ := e
    -- the running state after the first step satisfies its own fixpoint equation,
    -- hence equals d pointwise (it is trapped between d and itself)
    have h1 : sweep w E (step w d (x, y)) = step w d (x, y) := by
      apply le_antisymm (sweep_le w E _)
      intro v
      rw [← hfix]
      exact sweep_le w E (step w d (x, y)) v
    have hmem : (a, b) ∈ E := by
      rcases List.mem_cons.mp hab with h' | h'
      · exact absurd h' he
      · exact h'
    have := ih (step w d (x, y)) h1 a b hmem
    have ha : step w d (x, y) a = d a := by
      unfold step
      rw [Function.update_apply, if_neg (fun h' => he (by rw [Prod.mk.injEq]; exact ⟨h', rfl⟩))]
    have hb : step w d (x, y) b = d b := by
      unfold step
      rw [Function.update_apply, if_neg (fun h' => he (by rw [Prod.mk.injEq]; exact ⟨h', rfl⟩))]
    rw [ha, hb] at this
    exact this

theorem fixpoint_of_tight (w : V → V → ℕ) (E : List (V × V)) (d : V → ℕ)
    (htight : ∀ (a b : V), (a, b) ∈ E → d b ≤ d a + w a b) :
    sweep w E d = d := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    obtain ⟨x, y⟩ := e
    show sweep w E (step w d (x, y)) d = d
    have hstep : step w d (x, y) = d := by
      funext v
      unfold step
      rw [Function.update_apply]
      by_cases h : y = v
      · rw [if_pos h, h]
        exact congrArg _ (min_eq_left (htight x y (List.mem_cons.mpr (Or.inl rfl))))
      · rw [if_neg h]
    rw [hstep]
    exact ih

theorem sweepFix_iff (w : V → V → ℕ) (E : List (V × V)) (d : V → ℕ) :
    sweep w E d = d ↔ ∀ (a b : V), (a, b) ∈ E → d b ≤ d a + w a b :=
  ⟨tight_of_fixpoint w E d, fixpoint_of_tight w E d⟩

/-- Repeated sweeps: `sweepRun w E k d` is `k` sweeps from `d`. -/
def sweepRun (w : V → V → ℕ) (E : List (V × V)) : ℕ → (V → ℕ) → (V → ℕ)
  | 0, d => d
  | (k + 1), d => sweep w E (sweepRun w E k d)

theorem sweepRun_succ (w : V → V → ℕ) (E : List (V × V)) (k : ℕ) (d : V → ℕ) :
    sweepRun w E (k + 1) d = sweep w E (sweepRun w E k d) := rfl

/-- Running from an already-swept state is one extra sweep. -/
theorem sweepRun_sweep (w : V → V → ℕ) (E : List (V × V)) (k : ℕ) (d : V → ℕ) :
    sweepRun w E k (sweep w E d) = sweepRun w E (k + 1) d := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => show sweep w E (sweepRun w E k (sweep w E d)) = _; rw [ih]; rfl

end Widgets
