module

public import RequestProject.Euler.BanachFlowDerivative
public import RequestProject.Euler.BanachCompactQuadraticTaylor

/-! Actual material flow has a quadratic initial-data linearization
error uniformly on a whole reference time interval. This follows from
the genuine field Taylor estimate, true displacement control, and Gronwall. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem banachFlow_uniform_quadratic_linearization
    {f : E → E} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {K : ℝ≥0} (hLip : LipschitzOnWith K f U) {a : E} {ρ T : ℝ}
    (hρ : 0 < ρ) (hT : 0 ≤ T) {X : E → ℝ → E}
    (hX : IsBanachFlowOn f U (ball a ρ) T X)
    {A : ℝ → E →L[ℝ] E} (hAc : ContinuousOn A (Icc (0 : ℝ) T))
    (hA0 : A 0 = ContinuousLinearMap.id ℝ E)
    (hAd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt A ((fderiv ℝ f (X a u)).comp (A u)) u) :
    ∃ δ > 0, ∃ C > 0, ∀ h : E, ‖h‖ ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
      ‖banachFlowLinearizationError X a h A t‖ ≤ C * ‖h‖ ^ 2 := by
  have ha : a ∈ ball a ρ := mem_ball_self hρ
  have hpath : IsCompact ((X a) '' Icc (0 : ℝ) T) :=
    isCompact_Icc.image_of_continuousOn (hX.continuous a ha)
  have hpathU : (X a) '' Icc (0 : ℝ) T ⊆ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact hX.mem a ha u hu
  obtain ⟨L, r, hr, hTaylor⟩ := exists_uniform_quadratic_taylor_on_compact hU hf hpath hpathU
  let P : ℝ := Real.exp ((K : ℝ) * T)
  have hP : 0 < P := Real.exp_pos _
  let G : ℝ := |gronwallBound 0 (K : ℝ) 1 T| + 1
  have hG : 0 < G := by dsimp only [G]; positivity
  let C : ℝ := (L : ℝ) * P ^ 2 * G + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨min (ρ / 2) (r / P), lt_min (half_pos hρ) (div_pos hr hP), C, hC, ?_⟩
  intro h hh t ht
  have hah : a + h ∈ ball a ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact (hh.trans (min_le_left _ _)).trans_lt (half_lt_self hρ)
  have hdisp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      ‖X (a + h) u - X a u‖ ≤ P * ‖h‖ := hX.norm_displacement_le hLip ha hah hu
  have hrem (u : ℝ) (hu : u ∈ Ico (0 : ℝ) t) :
      ‖f (X (a + h) u) - f (X a u) - fderiv ℝ f (X a u) (X (a + h) u - X a u)‖ ≤
        (L : ℝ) * P ^ 2 * ‖h‖ ^ 2 := by
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.le.trans ht.2⟩
    have hsmall : ‖X (a + h) u - X a u‖ ≤ r := (hdisp u huT).trans (by
      have he := (le_div_iff₀ hP).mp (hh.trans (min_le_right _ _))
      simpa only [mul_comm] using he)
    have he := (hTaylor (X a u) ⟨u, huT, rfl⟩ (X (a + h) u - X a u) hsmall).2
    rw [show X a u + (X (a + h) u - X a u) = X (a + h) u by abel] at he
    calc
      _ ≤ (L : ℝ) * ‖X (a + h) u - X a u‖ ^ 2 := he
      _ ≤ (L : ℝ) * (P * ‖h‖) ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hdisp u huT) 2) L.coe_nonneg
      _ = _ := by ring
  have hsubset : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := fun _ hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hec : ContinuousOn (banachFlowLinearizationError X a h A) (Icc (0 : ℝ) t) :=
    (((hX.continuous (a + h) hah).sub (hX.continuous a ha)).sub
      (hAc.clm_apply continuousOn_const)).mono hsubset
  have he0 : banachFlowLinearizationError X a h A 0 = 0 := by
    simp only [banachFlowLinearizationError, hX.initial (a + h) hah, hX.initial a ha,
      hA0, ContinuousLinearMap.id_apply, add_sub_cancel_left, sub_self]
  have herr := norm_le_gronwallBound_of_norm_deriv_right_le hec
    (fun u hu => (banachFlowLinearizationError_hasDerivAt hX ha hah
      ⟨hu.1, hu.2.le.trans ht.2⟩ (hAd u ⟨hu.1, hu.2.le.trans ht.2⟩)).hasDerivWithinAt)
    (a := (0 : ℝ)) (b := t) (δ := 0) (ε := (L : ℝ) * P ^ 2 * ‖h‖ ^ 2) (K := (K : ℝ))
    (by rw [he0, norm_zero])
    (fun u hu => by
      have hB : ‖fderiv ℝ f (X a u)‖ ≤ K := norm_fderiv_le_of_lipschitzOn ℝ
        (hU.mem_nhds (hX.mem a ha u ⟨hu.1, hu.2.le.trans ht.2⟩)) hLip
      exact (norm_add_le _ _).trans (add_le_add
        (((fderiv ℝ f (X a u)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hB (norm_nonneg _))) (hrem u hu))) t ⟨ht.1, le_rfl⟩
  have hcoeff : gronwallBound 0 (K : ℝ) 1 t ≤ G := by
    have he := gronwallBound_mono (δ := 0) (ε := 1) (by norm_num) (by norm_num) K.coe_nonneg ht.2
    exact he.trans ((le_abs_self _).trans (by dsimp only [G]; linarith))
  calc
    _ ≤ gronwallBound 0 (K : ℝ) ((L : ℝ) * P ^ 2 * ‖h‖ ^ 2) t := by
      simpa only [sub_zero] using herr
    _ = ((L : ℝ) * P ^ 2 * ‖h‖ ^ 2) * gronwallBound 0 (K : ℝ) 1 t :=
      by unfold gronwallBound; split_ifs <;> ring
    _ ≤ ((L : ℝ) * P ^ 2 * ‖h‖ ^ 2) * G :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ ≤ C * ‖h‖ ^ 2 := by dsimp only [C]; nlinarith [sq_nonneg ‖h‖]

end Euler2D

end
