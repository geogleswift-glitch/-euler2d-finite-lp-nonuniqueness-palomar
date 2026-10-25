module

public import RequestProject.Euler.OsgoodStability
public import RequestProject.Euler.LogFlowGlobal

/-! Uniform spatial stability of actual trajectories with a common logarithmic modulus. -/

@[expose] public section

noncomputable section

open Set Filter Topology Real

namespace Euler2D

lemma logFlow_sq_distance_deriv_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {C : ℝ} (hC : 0 ≤ C) (x y vx vy : E) (hclose : ‖x - y‖ ≤ 1 / 2)
    (hv : ‖vx - vy‖ ≤ C * logFlowModulus ‖x - y‖) :
    2 * inner ℝ (x - y) (vx - vy) ≤ (2 * C) * logFlowModulus (‖x - y‖ ^ 2) := by
  let d := ‖x - y‖
  have hd : 0 ≤ d := norm_nonneg _
  have hi := (le_abs_self (inner ℝ (x - y) (vx - vy))).trans (abs_real_inner_le_norm _ _)
  have hb : 2 * inner ℝ (x - y) (vx - vy) ≤ 2 * (d * (C * logFlowModulus d)) :=
    (mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 2)).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hd) (by norm_num))
  change 2 * inner ℝ (x - y) (vx - vy) ≤ 2 * C * logFlowModulus (d ^ 2)
  by_cases hz : d = 0
  · rw [hz] at hb ⊢
    simpa [logFlowModulus] using hb
  · have hlog : Real.log d ≤ 0 := Real.log_nonpos hd (by dsimp only [d]; linarith)
    have hsign : 0 ≤ 2 * C * d ^ 2 * (-Real.log d) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg d))
        (neg_nonneg.mpr hlog)
    change 2 * inner ℝ (x - y) (vx - vy) ≤ 2 * C * (d ^ 2 - d ^ 2 * Real.log (d ^ 2))
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    dsimp only [logFlowModulus] at hb
    exact hb.trans (by nlinarith only [hsign])

/-- The initial-distance threshold is uniform over all velocities and
all trajectories with the specified common modulus and time interval. -/
theorem logFlow_uniform_stability {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T C ε : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (v : ℝ → E → E) (X Y : ℝ → E),
      Continuous X → Continuous Y →
      (∀ t ∈ Icc 0 T, HasDerivAt X (v t (X t)) t) →
      (∀ t ∈ Icc 0 T, HasDerivAt Y (v t (Y t)) t) →
      (∀ t ∈ Icc 0 T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
        ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) →
      ‖X 0 - Y 0‖ ≤ δ → ∀ t ∈ Icc 0 T, ‖X t - Y t‖ < ε := by
  let η := min (ε ^ 2) (1 / 4 : ℝ)
  have hη : 0 < η := lt_min (sq_pos_of_pos hε) (by norm_num)
  have hηquarter : η ≤ 1 / 4 := min_le_right _ _
  obtain ⟨d, hd, hbound⟩ := logFlow_small_initial hT
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)
    hη (hηquarter.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))
  refine ⟨Real.sqrt d, Real.sqrt_pos.mpr hd, fun v X Y hXc hYc hX hY hlip hinit t ht => ?_⟩
  let f := fun t => ‖X t - Y t‖ ^ 2
  let f' := fun t => 2 * inner ℝ (X t - Y t) (v t (X t) - v t (Y t))
  have hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t :=
    fun t ht => ((hX t ht).sub (hY t ht)).norm_sq
  have hinitSq : f 0 ≤ d := by
    dsimp only [f]
    nlinarith [norm_nonneg (X 0 - Y 0), Real.sq_sqrt hd.le]
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 T) (hfs : f s ≤ η) :
      f' s ≤ 2 * C * logFlowModulus (f s) := by
    have hsc : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.le⟩
    have hclose : ‖X s - Y s‖ ≤ 1 / 2 := by
      dsimp only [f] at hfs
      nlinarith [norm_nonneg (X s - Y s)]
    exact logFlow_sq_distance_deriv_le hC _ _ _ _ hclose (hlip s hsc _ _ hclose)
  have hsmall := hbound f f' ((hXc.sub hYc).norm.pow 2) hf
    (fun s _ => sq_nonneg _) hinitSq hderiv t ht
  have hηε : η ≤ ε ^ 2 := min_le_left _ _
  dsimp only [f] at hsmall
  nlinarith [norm_nonneg (X t - Y t)]

end Euler2D

end
