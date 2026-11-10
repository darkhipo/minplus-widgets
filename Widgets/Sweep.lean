import Mathlib.Logic.Function.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

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
  show (Function.update d e.2 (min (d e.2) (d e.1 + w e.1 e.2))) v ≤ d v
  rw [Function.update_apply]
  by_cases h : v = e.2
  · rw [if_pos h, h]
    omega
  · rw [if_neg h]
    exact Nat.le_refl _

theorem sweep_le (w : V → V → ℕ) (E : List (V × V)) (d : V → ℕ) (v : V) :
    sweep w E d v ≤ d v := by
  induction E generalizing d with
  | nil => exact Nat.le_refl _
  | cons e E ih =>
    have h1 : sweep w E (step w d e) v ≤ step w d e v := ih (step w d e)
    have h2 : step w d e v ≤ d v := step_le w d e v
    show sweep w E (step w d e) v ≤ d v
    omega

/-- Every value at `v` survives a sweep that never relaxes an edge into `v`. -/
theorem sweep_untouched (w : V → V → ℕ) : ∀ (E : List (V × V)) (d : V → ℕ) (v : V),
    (∀ z : V, (z, v) ∉ E) → sweep w E d v = d v := by
  intro E
  induction E with
  | nil => intro d v _; rfl
  | cons e E ih =>
    intro d v hf
    obtain ⟨x, y⟩ := e
    by_cases hy : v = y
    · exact (hf x (by rw [hy]; exact List.mem_cons_self)).elim
    · show sweep w E (step w d (x, y)) v = d v
      rw [ih (step w d (x, y)) v (fun z hz => hf z (List.mem_cons_of_mem _ hz))]
      show (Function.update d y (min (d y) (d x + w x y))) v = d v
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
    rcases List.mem_cons.mp h with h'' | h'
    · rw [Prod.mk.injEq] at h''
      obtain ⟨hax, hby⟩ := h''
      rw [hax, hby]
      have h2 : step w d (x, y) y ≤ d x + w x y := by
        show (Function.update d y (min (d y) (d x + w x y))) y ≤ d x + w x y
        rw [Function.update_apply, if_pos rfl]
        omega
      have h1 : sweep w E (step w d (x, y)) y ≤ step w d (x, y) y :=
        sweep_le w E (step w d (x, y)) y
      omega
    · have h1 : sweep w E (step w d (x, y)) b ≤ step w d (x, y) b :=
        sweep_le w E (step w d (x, y)) b
      have h2 := ih (step w d (x, y)) a b h'
      have h3 : step w d (x, y) a + w a b ≤ d a + w a b :=
        Nat.add_le_add_right (step_le w d (x, y) a) _
      omega

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
    have hE : sweep w E (step w d (x, y)) = d := hfix
    have hr' : step w d (x, y) = d := by
      funext v
      have h1 : step w d (x, y) v ≤ d v := step_le w d (x, y) v
      have h2 : d v ≤ step w d (x, y) v := by
        have hle := sweep_le w E (step w d (x, y)) v
        rwa [hE] at hle
      exact Nat.le_antisymm h1 h2
    rcases List.mem_cons.mp hab with h' | h'
    · have h'2 : a = x ∧ b = y := by rw [Prod.mk.injEq] at h'; exact h'
      obtain ⟨hax, hby⟩ := h'2
      rw [hax, hby]
      have e1 : d y = sweep w E (step w d (x, y)) y := (congrFun hE y).symm
      have e2 : sweep w E (step w d (x, y)) y ≤ step w d (x, y) y :=
        sweep_le w E (step w d (x, y)) y
      have e3 : step w d (x, y) y = min (d y) (d x + w x y) := by
        show (Function.update d y (min (d y) (d x + w x y))) y = min (d y) (d x + w x y)
        rw [Function.update_apply, if_pos rfl]
      omega
    · have hfix' : sweep w E (step w d (x, y)) = step w d (x, y) := hE.trans hr'.symm
      have hres := ih (step w d (x, y)) hfix' a b h'
      rwa [hr'] at hres

theorem fixpoint_of_tight (w : V → V → ℕ) (E : List (V × V)) (d : V → ℕ)
    (htight : ∀ (a b : V), (a, b) ∈ E → d b ≤ d a + w a b) :
    sweep w E d = d := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    obtain ⟨x, y⟩ := e
    show sweep w E (step w d (x, y)) = d
    have hstep : step w d (x, y) = d := by
      funext v
      show (Function.update d y (min (d y) (d x + w x y))) v = d v
      rw [Function.update_apply]
      by_cases h : v = y
      · rw [if_pos h, h]
        have hle : d y ≤ d x + w x y := htight x y (List.mem_cons.mpr (Or.inl rfl))
        omega
      · rw [if_neg h]
    rw [hstep]
    have htail : sweep w E d = d :=
      ih (fun a b hab' => htight a b (List.mem_cons_of_mem _ hab'))
    exact htail

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
  | succ k ih =>
      show sweep w E (sweepRun w E k (sweep w E d)) = sweep w E (sweepRun w E (k + 1) d)
      rw [ih]

#print axioms step_le
#print axioms sweep_le
#print axioms sweep_hit
#print axioms sweepFix_iff
#print axioms sweepRun_sweep

end Widgets
