import Mathlib.Tactic

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

theorem range_nonempty' (t : ℕ) : (Finset.range (t + 1)).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ t)⟩

/-! ### The convolution and its two characterizations -/

/-- Discrete min-plus convolution: `(α ⊛ β) t = min_{s ≤ t} (α s + β (t - s))`. -/
def mpConv (α β : ℕ → ℕ) (t : ℕ) : ℕ :=
  ((Finset.range (t + 1)).image fun s => α s + β (t - s)).min'
    (range_nonempty' t).image

theorem mpConv_le (α β : ℕ → ℕ) {t s : ℕ} (h : s ≤ t) :
    mpConv α β t ≤ α s + β (t - s) := by
  unfold mpConv
  exact Finset.min'_le _ (Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (Nat.succ_le_succ h), rfl⟩)

theorem le_mpConv (α β : ℕ → ℕ) {t x : ℕ} (h : ∀ s ≤ t, x ≤ α s + β (t - s)) :
    x ≤ mpConv α β t := by
  unfold mpConv
  refine Finset.le_min' _ ?_
  rintro y ⟨s, hs, rfl⟩
  exact h s (Finset.mem_range.mp hs)

/-- The `min'`-over-image shifts a constant across the addition. -/
private theorem min'_image_add_const (S : Finset ℕ) (hS : S.Nonempty) (c : ℕ) (f : ℕ → ℕ) :
    ((S.image fun i => c + f i)).min' hS.image = c + ((S.image f)).min' hS.image := by
  refine le_antisymm (Finset.le_min' _ fun x hx => ?_) (Finset.le_min' _ fun x hx => ?_)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.min'_le _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.min'_le _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

/-! ### The min-plus algebra -/

theorem mpConv_comm (α β : ℕ → ℕ) (t : ℕ) : mpConv α β t = mpConv β α t := by
  unfold mpConv
  refine congrArg _ (le_antisymm ?_ ?_)
  · rw [Finset.image_subset_iff]
    intro s hs
    have hst : s ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    refine Finset.mem_image.mpr ⟨t - s, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_sub_self hst, Nat.add_comm]
  · rw [Finset.image_subset_iff]
    intro s hs
    have hst : s ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    refine Finset.mem_image.mpr ⟨t - s, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.sub_sub_self hst, Nat.add_comm]

theorem mpConv_assoc (α β γ : ℕ → ℕ) (t : ℕ) :
    mpConv (mpConv α β) γ t = mpConv α (mpConv β γ) t := by
  refine le_antisymm ?_ ?_
  · -- LHS ≤ RHS: at every outer index s ≤ t, through the witness window s + w
    refine Finset.le_min' _ fun s hs => ?_
    have hst : s ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
    calc mpConv (mpConv α β) γ t
        ≤ ((Finset.range (t - s + 1)).image fun w => α s + (β w + γ (t - s - w))).min'
            (range_nonempty' _).image := by
        refine Finset.le_min' _ fun w hw => ?_
        have hws : w ≤ t - s := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
        have h1 : mpConv (mpConv α β) γ t ≤ mpConv α β (s + w) + γ (t - (s + w)) :=
          mpConv_le _ _ (by omega)
        have h2 : mpConv α β (s + w) ≤ α s + β (s + w - s) :=
          mpConv_le α β (Nat.le_add_right s w)
        have h3 : t - (s + w) = t - s - w := by omega
        have h4 : s + w - s = w := Nat.add_sub_cancel_left
        calc mpConv (mpConv α β) γ t
            ≤ mpConv α β (s + w) + γ (t - (s + w)) := h1
          _ = mpConv α β (s + w) + γ (t - s - w) := by rw [h3]
          _ ≤ (α s + β w) + γ (t - s - w) := by
                rw [h4] at h2
                exact add_le_add_right h2 _
          _ = α s + (β w + γ (t - s - w)) := by ring
      _ = α s + mpConv β γ (t - s) := by rw [min'_image_add_const]
  · -- RHS ≤ LHS: at every outer index s' ≤ t, through the inner witness s' - u
    refine Finset.le_min' _ fun s' hs' => ?_
    have hs't : s' ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hs')
    calc mpConv α (mpConv β γ) t
        ≤ ((Finset.range (s' + 1)).image fun u => α u + β (s' - u) + γ (t - s')).min'
            (range_nonempty' _).image := by
        refine Finset.le_min' _ fun u hu => ?_
        have hus' : u ≤ s' := Nat.le_of_lt_succ (Finset.mem_range.mp hu)
        have h1 : mpConv α (mpConv β γ) t ≤ α u + mpConv β γ (t - u) :=
          mpConv_le _ _ (by omega)
        have h2 : mpConv β γ (t - u) ≤ β (s' - u) + γ (t - u - (s' - u)) :=
          mpConv_le β γ (by omega)
        have h3 : t - u - (s' - u) = t - s' := by omega
        calc mpConv α (mpConv β γ) t
            ≤ α u + mpConv β γ (t - u) := h1
          _ ≤ α u + (β (s' - u) + γ (t - s')) := by
                rw [h3] at h2
                exact add_le_add_right h2 _
          _ = α u + β (s' - u) + γ (t - s') := by ring
      _ = mpConv α β s' + γ (t - s') := by rw [min'_image_add_const]

theorem mpConv_mono_right (α β β' : ℕ → ℕ) (h : ∀ s, β s ≤ β' s) (t : ℕ) :
    mpConv α β t ≤ mpConv α β' t := by
  refine le_mpConv α β' fun s hs => ?_
  exact le_trans (mpConv_le α β hs) (add_le_add_left (h (t - s)) _)

theorem mpConv_mono_left (α α' β : ℕ → ℕ) (h : ∀ s, α s ≤ α' s) (t : ℕ) :
    mpConv α β t ≤ mpConv α' β t := by
  rw [mpConv_comm, mpConv_comm α' β]
  exact mpConv_mono_right β α α' h t

/-! ### Closure and the delay bound -/

/-- Subadditive curves (with `α 0 = 0`) are closed under self-convolution —
the arrival-curve closure law of the min-plus calculus. -/
theorem mpConv_self_le (α : ℕ → ℕ) (h0 : α 0 = 0) (t : ℕ) : mpConv α α t ≤ α t := by
  refine (mpConv_le α α t (Nat.le_refl t)).trans ?_
  rw [Nat.sub_self, h0, Nat.zero_add]

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
    (hf0 : f 0 = 0)
    (hN : ∀ v, α v ≤ β v + N)
    (t : ℕ) : f t ≤ g t + N := by
  have h1 : mpConv f β t ≤ β t := by
    refine (mpConv_le f β (Nat.zero_le t)).trans ?_
    rw [hf0, Nat.sub_zero, Nat.zero_add]
  calc f t ≤ f 0 + α (t - 0) := hfA 0 t (Nat.zero_le t)
    _ = α t := by rw [hf0, Nat.sub_zero, Nat.zero_add]
    _ ≤ β t + N := hN t
    _ ≤ g t + N := by rw [add_le_add_iff_right]; exact le_trans h1 (hsvc t)

end Widgets.NetCalc
