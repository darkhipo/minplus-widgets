import Widgets.Sweep

/-!
# Widgets.TriangularBatch — the one-batch-pass settle license

A **triangular** min-plus system is an edge list whose in-edges all precede
the out-edges of every vertex (a topologically ordered DAG, no duplicate
edges — cycles and self-loops are excluded by the ordering condition
itself).  The license: *one* sweep in the stored order settles the whole
system — the swept state satisfies every Bellman inequality on the list.

This is the min-plus form of the ordering/contraction mechanism of

  S. Luo, H. Zhao, *Convergence analysis of the fast sweeping method for
  static convex Hamilton–Jacobi equations*, Res. Math. Sci. 3:33 (2016):

one Gauss–Seidel pass along a causal ordering propagates information
exactly once through the dependency order.  Feeds the APSP product-round
bracket/triangular structure and the segmented assembly: a triangular
block needs a single batch pass, not an iteration loop.

Credit: Luo–Zhao 2016 (ordering + contraction); formalization ours.
-/

namespace Widgets

variable {V : Type*} [DecidableEq V]

/-- Triangular edge list: no duplicate edges, and every edge into `y`
precedes every edge out of `y` in the list order. -/
structure Triangular (E : List (V × V)) : Prop where
  nodup : E.Nodup
  inBeforeOut : ∀ (x y z : V), (x, y) ∈ E → (y, z) ∈ E → E.idxOf (x, y) < E.idxOf (y, z)

theorem Triangular.noSelfLoop {E : List (V × V)} (htri : Triangular E) {a b : V}
    (hab : (a, b) ∈ E) : a ≠ b := by
  intro h
  subst h
  have := htri.inBeforeOut a a a hab hab
  exact absurd this (Nat.lt_irrefl _)

/-- First-occurrence position: an edge of the left part sits before `|P|`. -/
private theorem idxOf_mem_left_le {α : Type*} [BEq α] [LawfulBEq α] {P E' : List α}
    {u : α} (hu : u ∈ P) : (P ++ E').idxOf u ≤ P.length := by
  rw [List.idxOf_append, if_pos hu]
  exact Nat.le_of_lt (List.idxOf_lt_length hu)

/-- First-occurrence position: an edge only of the right part sits at `≥ |P|`. -/
private theorem length_le_idxOf_mem_right {α : Type*} [BEq α] [LawfulBEq α]
    {P E' : List α} {u : α} (huP : u ∉ P) (huE : u ∈ E') :
    P.length ≤ (P ++ E').idxOf u := by
  rw [List.idxOf_append, if_neg huP]
  exact Nat.le_add_left _ _

/-- One pass settles the processed prefix tightly, by induction along the
stored order.  (The carried invariant: heads of processed edges are never
targeted by the unprocessed suffix — that is exactly what `Triangular`
buys.) -/
private theorem onePass_aux (w : V → V → ℕ) {F : List (V × V)} (htri : Triangular F) :
    ∀ (E' P : List (V × V)), P ++ E' = F → ∀ r : V → ℕ,
    (∀ (a b : V), (a, b) ∈ P → ∀ z : V, (z, b) ∉ E') →
    (∀ (a b : V), (a, b) ∈ P → r b ≤ r a + w a b) →
    ∀ (a b : V), (a, b) ∈ P ++ E' →
      sweep w E' r b ≤ sweep w E' r a + w a b := by
  intro E'
  induction E' with
  | nil =>
    intro P _ r _ htight a b hab
    rw [List.append_nil] at hab ⊢
    exact htight a b hab
  | cons e E' ih =>
    intro P hsplit r hfrozen htight a b hab
    obtain ⟨x, y⟩ := e
    have hmemXY : (x, y) ∈ F := by
      rw [← hsplit]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self ..))
    -- the head of the current edge is never targeted by the unprocessed tail
    have hnofreeze : ∀ z : V, (z, x) ∉ E' := by
      intro z hz
      have hzx : (z, x) ∈ F := by
        rw [← hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hz))
      have hzxP : (z, x) ∉ P := fun hp =>
        (List.nodup_append.mp htri.nodup).2.2 (z, x) hp hz
      have h1 := htri.inBeforeOut z x y hzx hmemXY
      have h3 : F.idxOf (x, y) ≤ P.length := by
        rw [← hsplit]
        by_cases hp : (x, y) ∈ P
        · exact idxOf_mem_left_le hp
        · rw [List.idxOf_append, if_neg hp, List.idxOf_cons_self, Nat.zero_add]
      have h4 : P.length ≤ F.idxOf (z, x) := by
        rw [← hsplit]
        exact length_le_idxOf_mem_right hzxP hz
      omega
    set r' : V → ℕ := step w r (x, y) with hr'
    -- the new frozen condition for the grown prefix
    have hfrozen' : ∀ (a b : V), (a, b) ∈ P ++ [(x, y)] → ∀ z : V, (z, b) ∉ E' := by
      intro a b hab z hz
      rcases List.mem_append.mp hab with hp | hp
      · exact hfrozen a b hp z hz
      · have heq : (a, b) = (x, y) := List.mem_singleton.mp hp
        rw [heq] at hz ⊢
        exact hnofreeze z hz
    -- the new tightness for the grown prefix, at the advanced state
    have hyx : y ≠ x := fun h => htri.noSelfLoop hmemXY h.symm
    have htight' : ∀ (a b : V), (a, b) ∈ P ++ [(x, y)] → r' b ≤ r' a + w a b := by
      intro a b hab
      rcases List.mem_append.mp hab with hp | hp
      · have hay : y ≠ a := fun h => hfrozen a b hp x (by rw [← h]; exact List.mem_cons_self ..)
        have hby : y ≠ b := fun h => hfrozen a b hp x (by rw [← h]; exact List.mem_cons_self ..)
        show step w r (x, y) b ≤ step w r (x, y) a + w a b
        unfold step
        rw [Function.update_apply, if_neg hby, Function.update_apply, if_neg hay]
        exact htight a b hp
      · have heq : (a, b) = (x, y) := List.mem_singleton.mp hp
        subst heq
        show step w r (x, y) y ≤ step w r (x, y) x + w x y
        unfold step
        rw [Function.update_apply, if_pos rfl, Function.update_apply,
          if_neg (fun h : x = x => hyx h.symm)]
        exact min_le_right _ _
    -- membership transport and the induction hypothesis
    have hsplit' : P ++ [(x, y)] ++ E' = F := by
      rw [List.append_assoc, List.singleton_append, hsplit]
    have := ih (P ++ [(x, y)]) hsplit' r' hfrozen' htight'
    intro a' b' hab'
    rw [List.append_assoc, List.singleton_append] at hab'
    exact this a' b' hab'

/-- **One-batch-pass settle license** (Luo–Zhao 2016, min-plus form): a single
sweep along a triangular edge list leaves the state satisfying every Bellman
inequality on the list — no iteration, no second pass. -/
theorem onePass_tight (w : V → V → ℕ) {E : List (V × V)} (htri : Triangular E)
    (d₀ : V → ℕ) (a b : V) (hab : (a, b) ∈ E) :
    sweep w E d₀ b ≤ sweep w E d₀ a + w a b := by
  refine onePass_aux w htri E [] (by rw [List.append_nil]) d₀ ?_ ?_ a b ?_
  · intro a b hab; exact absurd hab (by simp)
  · intro a b hab; exact absurd hab (by simp)
  · simpa using hab

end Widgets
