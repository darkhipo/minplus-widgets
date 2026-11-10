import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Order.Basic

/-!
# Widgets.NetCalc — certified discrete min-plus network calculus

The named min-plus calculus lemmas, in ℕ so our Bound-arithmetic can cite
them directly (no ℝ, no ⊤):

* `mpConv` — the discrete min-plus (inf-)convolution
  `(α ⊛ β) t = min_{s ≤ t} (α s + β (t - s))`;
* `mpConv_comm`, `mpConv_assoc` — the min-plus algebra (associativity is
  THE structural lemma of the calculus);
* `mpConv_mono_left/right` — monotonicity;
* `mpConv_self_le` — subadditive curves are closed under self-convolution
  (`(α ⊛ α) ≤ α` for `α 0 = 0`), the arrival-curve closure law;
* `serviceCurve_backlog` — **service curve ⇒ delay bound**: if the system
  guarantees output `≥ f ⊛ β` (β a min-plus service curve) and `f` is
  constrained by the arrival curve `α` (leaky-bucket form), then the
  backlog `f t - g t` is bounded by `N` for any `N` dominating the vertical
  deviation `h(α, β)`, i.e. `∀ v, α v ≤ β v + N`.

Credit: the min-plus network-calculus lineage — R. Cruz 1991; C.-S. Chang,
*Performance Guarantees in Communication Networks* 2000; J.-Y. Le Boudec &
P. Thiran, *Network Calculus* (LNCS 2050) 2001.  Discrete-ℕ statements and
proofs ours.
-/

namespace Widgets.NetCalc

/-! ### Fold-level helpers: min over a list -/

/-- Any term of a `min`-fold is above the fold. -/
theorem foldr_min_le {l : List ℕ} {seed : ℕ} {f : ℕ → ℕ} {s : ℕ} (hs : s ∈ l) :
    l.foldr (fun i acc => min (f i) acc) seed ≤ f s := by
  induction l with
  | nil => cases hs
  | cons hd tl ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hs with rfl | hmem
    · exact Nat.min_le_left _ _
    · exact Nat.le_trans (Nat.min_le_right _ _) (ih hmem)

/-- If `x` is below every term of a `min`-fold, it is below the fold. -/
theorem le_foldr_min {l : List ℕ} {seed : ℕ} {f : ℕ → ℕ} {x : ℕ}
    (hx : x ≤ seed) (h : ∀ s ∈ l, x ≤ f s) :
    x ≤ l.foldr (fun i acc => min (f i) acc) seed := by
  induction l with
  | nil => exact hx
  | cons hd tl ih =>
    rw [List.foldr_cons]
    exact Nat.le_min.mpr ⟨h hd List.mem_cons_self,
      ih (fun s hmem => h s (List.mem_cons_of_mem _ hmem))⟩

/-- A constant on the left distributes into a `min`-fold. -/
theorem add_foldr_min_left (c : ℕ) (l : List ℕ) (f : ℕ → ℕ) (seed : ℕ) :
    c + l.foldr (fun i acc => min (f i) acc) seed
      = l.foldr (fun i acc => min (c + f i) acc) (c + seed) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldr_cons, List.foldr_cons]
    rcases Nat.le_total (f hd) (tl.foldr (fun i acc => min (f i) acc) seed) with hle | hle
    · have h2 : c + f hd ≤ tl.foldr (fun i acc => min (c + f i) acc) (c + seed) := by
        rw [← ih]
        exact Nat.add_le_add_left hle c
      rw [Nat.min_eq_left hle, Nat.min_eq_left h2]
    · have h2 : tl.foldr (fun i acc => min (c + f i) acc) (c + seed) ≤ c + f hd := by
        rw [← ih]
        exact Nat.add_le_add_left hle c
      rw [Nat.min_eq_right hle, Nat.min_eq_right h2]
      exact ih

/-- A constant on the right distributes into a `min`-fold. -/
theorem add_foldr_min_right (c : ℕ) (l : List ℕ) (f : ℕ → ℕ) (seed : ℕ) :
    l.foldr (fun i acc => min (f i) acc) seed + c
      = l.foldr (fun i acc => min (f i + c) acc) (seed + c) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldr_cons, List.foldr_cons]
    rcases Nat.le_total (f hd) (tl.foldr (fun i acc => min (f i) acc) seed) with hle | hle
    · have h2 : f hd + c ≤ tl.foldr (fun i acc => min (f i + c) acc) (seed + c) := by
        rw [← ih]
        exact Nat.add_le_add_right hle c
      rw [Nat.min_eq_left hle, Nat.min_eq_left h2]
    · have h2 : tl.foldr (fun i acc => min (f i + c) acc) (seed + c) ≤ f hd + c := by
        rw [← ih]
        exact Nat.add_le_add_right hle c
      rw [Nat.min_eq_right hle, Nat.min_eq_right h2]
      exact ih

/-! ### The convolution and its two characterizations -/

/-- Discrete min-plus convolution: the minimum of `α s + β (t - s)` over
`s ≤ t` (the seed is the `s = t` term itself). -/
def mpConv (α β : ℕ → ℕ) (t : ℕ) : ℕ :=
  (List.range (t + 1)).foldr (fun s acc => min (α s + β (t - s)) acc) (α t + β (t - t))

theorem mpConv_le (α β : ℕ → ℕ) {t s : ℕ} (h : s ≤ t) :
    mpConv α β t ≤ α s + β (t - s) := by
  unfold mpConv
  refine foldr_min_le ?_
  rw [List.mem_range]
  omega

theorem le_mpConv (α β : ℕ → ℕ) {t x : ℕ} (h : ∀ s ≤ t, x ≤ α s + β (t - s)) :
    x ≤ mpConv α β t := by
  unfold mpConv
  refine le_foldr_min ?_ ?_
  · have hse : x ≤ α t + β (t - t) := h t (Nat.le_refl t)
    simpa using hse
  · intro s hs
    rw [List.mem_range] at hs
    exact h s (by omega)

/-! ### The min-plus algebra -/

theorem mpConv_comm (α β : ℕ → ℕ) (t : ℕ) : mpConv α β t = mpConv β α t := by
  refine Nat.le_antisymm ?_ ?_
  · refine le_mpConv β α ?_
    intro s hs
    have h := mpConv_le α β (t := t) (s := t - s) (by omega)
    rw [show t - (t - s) = s from Nat.sub_sub_self hs] at h
    omega
  · refine le_mpConv α β ?_
    intro s hs
    have h := mpConv_le β α (t := t) (s := t - s) (by omega)
    rw [show t - (t - s) = s from Nat.sub_sub_self hs] at h
    omega

theorem mpConv_assoc (α β γ : ℕ → ℕ) (t : ℕ) :
    mpConv (mpConv α β) γ t = mpConv α (mpConv β γ) t := by
  refine Nat.le_antisymm ?_ ?_
  · -- LHS ≤ RHS: at every outer index s ≤ t, through the witness window s + w
    refine le_mpConv α (mpConv β γ) ?_
    intro s hs
    -- rewrite α s + mpConv β γ (t - s) into a min-fold over w
    have hfold : α s + mpConv β γ (t - s)
        = (List.range (t - s + 1)).foldr
            (fun w acc => min (α s + (β w + γ (t - s - w))) acc)
            (α s + (β (t - s) + γ (t - s - (t - s)))) := by
      unfold mpConv
      rw [add_foldr_min_left]
    rw [hfold]
    refine le_foldr_min ?_ ?_
    · -- seed: LHS ≤ α s + (β (t-s) + γ (t-s-(t-s)))
      have h1 : mpConv (mpConv α β) γ t ≤ mpConv α β (s + (t - s)) + γ (t - (s + (t - s))) :=
        mpConv_le _ _ (by omega)
      have h2 : mpConv α β (s + (t - s)) ≤ α s + β (s + (t - s) - s) :=
        mpConv_le α β (by omega)
      rw [show s + (t - s) = t from by omega] at h1 h2
      rw [show t - t = t - s - (t - s) from by omega] at h1
      omega
    · intro w hw
      rw [List.mem_range] at hw
      have h1 : mpConv (mpConv α β) γ t ≤ mpConv α β (s + w) + γ (t - (s + w)) :=
        mpConv_le _ _ (by omega)
      have h2 : mpConv α β (s + w) ≤ α s + β (s + w - s) :=
        mpConv_le α β (by omega)
      rw [show s + w - s = w from by omega] at h2
      rw [show t - (s + w) = t - s - w from by omega] at h1
      omega
  · -- RHS ≤ LHS: at every outer index s' ≤ t, through the inner witness s' - u
    refine le_mpConv (mpConv α β) γ ?_
    intro s' hs'
    have hfold : mpConv α β s' + γ (t - s')
        = (List.range (s' + 1)).foldr
            (fun u acc => min ((α u + β (s' - u)) + γ (t - s')) acc)
            ((α s' + β (s' - s')) + γ (t - s')) := by
      unfold mpConv
      rw [add_foldr_min_right]
    rw [hfold]
    refine le_foldr_min ?_ ?_
    · have h1 : mpConv α (mpConv β γ) t ≤ α s' + mpConv β γ (t - s') :=
        mpConv_le _ _ (by omega)
      have h2 : mpConv β γ (t - s') ≤ β (s' - s') + γ (t - s' - (s' - s')) :=
        mpConv_le β γ (by omega)
      rw [show t - s' - (s' - s') = t - s' from by omega] at h2
      omega
    · intro u hu
      rw [List.mem_range] at hu
      have h1 : mpConv α (mpConv β γ) t ≤ α u + mpConv β γ (t - u) :=
        mpConv_le _ _ (by omega)
      have h2 : mpConv β γ (t - u) ≤ β (s' - u) + γ (t - u - (s' - u)) :=
        mpConv_le β γ (by omega)
      rw [show t - u - (s' - u) = t - s' from by omega] at h2
      omega

theorem mpConv_mono_right (α β β' : ℕ → ℕ) (h : ∀ s, β s ≤ β' s) (t : ℕ) :
    mpConv α β t ≤ mpConv α β' t := by
  refine le_mpConv α β' ?_
  intro s hs
  exact Nat.le_trans (n := mpConv α β t) (m := α s + β (t - s))
    (k := α s + β' (t - s)) (mpConv_le α β hs) (Nat.add_le_add_left (h (t - s)) (α s))

theorem mpConv_mono_left (α α' β : ℕ → ℕ) (h : ∀ s, α s ≤ α' s) (t : ℕ) :
    mpConv α β t ≤ mpConv α' β t := by
  rw [mpConv_comm, mpConv_comm α' β]
  exact mpConv_mono_right β α α' h t

/-! ### Closure and the delay bound -/

/-- Subadditive curves (with `α 0 = 0`) are closed under self-convolution —
the arrival-curve closure law of the min-plus calculus. -/
theorem mpConv_self_le (α : ℕ → ℕ) (h0 : α 0 = 0) (t : ℕ) : mpConv α α t ≤ α t := by
  have h := mpConv_le α α (t := t) (s := t) (Nat.le_refl t)
  rw [Nat.sub_self, h0, Nat.add_zero] at h
  exact h

/-- **Service curve ⇒ backlog bound.**  If the system's output dominates the
min-plus convolution with the service curve `β` (`hsvc`), the input `f` is
constrained by the arrival curve `α` in leaky-bucket form (`hfA`), and `N`
dominates the vertical deviation `h(α, β)` (`hN`), then the backlog at
every instant is at most `N`: `f t ≤ g t + N`.  (In the discrete window the
`s = 0` convolution term carries `β t`, so no subadditivity premise is
needed — the discrete transcription is strictly simpler than the
continuous one.) -/
theorem serviceCurve_backlog {f g α β : ℕ → ℕ} (N : ℕ)
    (hsvc : ∀ t, mpConv f β t ≤ g t)
    (hfA : ∀ u t, u ≤ t → f t ≤ f u + α (t - u))
    (_hf0 : f 0 = 0)
    (hN : ∀ v, α v ≤ β v + N)
    (t : ℕ) : f t ≤ g t + N := by
  have hkey : f t ≤ mpConv f β t + N := by
    unfold mpConv
    rw [add_foldr_min_right]
    refine le_foldr_min ?_ ?_
    · omega
    · intro s hs
      rw [List.mem_range] at hs
      have h1 := hfA s t (by omega)
      have h2 := hN (t - s)
      omega
  exact Nat.le_trans (n := f t) (m := mpConv f β t + N) (k := g t + N) hkey
    (Nat.add_le_add_right (hsvc t) N)

#print axioms mpConv_comm
#print axioms mpConv_assoc
#print axioms mpConv_mono_right
#print axioms mpConv_self_le
#print axioms serviceCurve_backlog

end Widgets.NetCalc
