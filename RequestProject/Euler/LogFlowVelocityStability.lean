module

public import RequestProject.Euler.LogFlowStability

/-! Genuine Osgood stability under a uniformly small perturbation
of the velocity. This proves convergence to the actual unique particle
flow on the entire plane without selecting a different limit for each
initial point. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric Real

namespace Euler2D

theorem logFlow_uniform_velocity_stability
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T C ε : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (v w : ℝ → E → E) (X Y : ℝ → E),
      Continuous X → Continuous Y →
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt X (v t (X t)) t) →
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Y (w t (Y t)) t) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
        ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) →
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x : E, ‖v t x - w t x‖ ≤ δ) →
      X 0 = Y 0 → ∀ t ∈ Icc (0 : ℝ) T, ‖X t - Y t‖ < ε := by
  let η := min (ε ^ 2) (1 / 4 : ℝ)
  have hη : 0 < η := lt_min (sq_pos_of_pos hε) (by norm_num)
  have hηquarter : η ≤ 1 / 4 := min_le_right _ _
  have hηε : η ≤ ε ^ 2 := min_le_left _ _
  have hC1 : 0 ≤ 2 * C + 1 := by linarith
  obtain ⟨d, hd, hsmall⟩ := logFlow_small_initial hT hC1 hη (hηquarter.trans (by norm_num))
  let δ := min d (η / 2)
  have hδ : 0 < δ := lt_min hd (half_pos hη)
  refine ⟨δ, hδ, ?_⟩
  intro v w X Y hXc hYc hXd hYd hmod hdiff hinit t ht
  let f : ℝ → ℝ := fun s => ‖X s - Y s‖ ^ 2
  let g : ℝ → ℝ := fun s => f s + δ
  let g' : ℝ → ℝ := fun s => 2 * inner ℝ (X s - Y s) (v s (X s) - w s (Y s))
  have hgc : Continuous g := ((hXc.sub hYc).norm.pow 2).add continuous_const
  have hgd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : HasDerivAt g (g' s) s :=
    (((hXd s hs).sub (hYd s hs)).norm_sq).add_const δ
  have hgnonneg (s : ℝ) : 0 ≤ g s := add_nonneg (sq_nonneg _) hδ.le
  have hginit : g 0 ≤ d := by
    dsimp only [g, f]
    rw [hinit, sub_self, norm_zero]
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] using min_le_left d (η / 2)
  have hbound (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) T) (hgs : g s ≤ η) :
      g' s ≤ (2 * C + 1) * logFlowModulus (g s) := by
    have hscc : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    have hfs : 0 ≤ f s := sq_nonneg _
    have hfg : f s ≤ g s := by dsimp only [g]; linarith [hδ.le]
    have hclose : ‖X s - Y s‖ ≤ 1 / 2 := by
      have hd0 := norm_nonneg (X s - Y s)
      dsimp only [f] at hfg
      nlinarith
    have hmain := logFlow_sq_distance_deriv_le hC (X s) (Y s) (v s (X s)) (v s (Y s))
      hclose (hmod s hscc _ _ hclose)
    have hrest : 2 * inner ℝ (X s - Y s) (v s (Y s) - w s (Y s)) ≤ δ := by
      have hi := (le_abs_self (inner ℝ (X s - Y s) (v s (Y s) - w s (Y s)))).trans
        (abs_real_inner_le_norm _ _)
      have hm := mul_le_mul_of_nonneg_left (hdiff s hscc (Y s)) (norm_nonneg (X s - Y s))
      nlinarith
    have hsplit : g' s =
        2 * inner ℝ (X s - Y s) (v s (X s) - v s (Y s)) +
        2 * inner ℝ (X s - Y s) (v s (Y s) - w s (Y s)) := by
      dsimp only [g']
      rw [show v s (X s) - w s (Y s) =
        (v s (X s) - v s (Y s)) + (v s (Y s) - w s (Y s)) by abel, inner_add_right]
      ring
    have hmono : logFlowModulus (f s) ≤ logFlowModulus (g s) :=
      monotoneOn_logFlowModulus ⟨hfs, by linarith⟩ ⟨hgnonneg s, by linarith⟩ hfg
    have hlog : Real.log (g s) ≤ 0 := Real.log_nonpos (hgnonneg s) (by linarith)
    have hmodlarge : δ ≤ logFlowModulus (g s) := by
      have hsign := mul_nonpos_of_nonneg_of_nonpos (hgnonneg s) hlog
      have hδg : δ ≤ g s := by dsimp only [g]; linarith
      dsimp only [logFlowModulus]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hmono (by linarith : 0 ≤ 2 * C)
    rw [hsplit]
    change _ ≤ (2 * C + 1) * logFlowModulus (g s)
    change 2 * inner ℝ (X s - Y s) (v s (X s) - v s (Y s)) ≤ 2 * C * logFlowModulus (f s) at hmain
    nlinarith
  have hgsmall := hsmall g g' hgc hgd (fun s _ => hgnonneg s) hginit hbound t ht
  dsimp only [g, f] at hgsmall
  nlinarith [norm_nonneg (X t - Y t)]

end Euler2D

end
