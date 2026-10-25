module

public import RequestProject.Euler.GlobalPlanarEulerBounds

/-! The genuine weighted conjugate fourth spatial moment. Compact
support makes its defining integral integrable. Strong L1 stability
with a common support radius gives continuity of this actual moment. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

def planarFourthMomentIntegrand (w : R2 → ℝ) (x : R2) : ℂ :=
  (w x : ℂ) * (star (complexPhysicalPlane.symm x)) ^ 4

def planarFourthMoment (w : R2 → ℝ) : ℂ := ∫ x, planarFourthMomentIntegrand w x

theorem norm_planarFourthMomentIntegrand_le {w : R2 → ℝ} {R : ℝ}
    (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R) (x : R2) :
    ‖planarFourthMomentIntegrand w x‖ ≤ ‖w x‖ * R ^ 4 := by
  by_cases hw : w x = 0
  · simp [planarFourthMomentIntegrand, hw]
  · have hb : ‖x‖ ^ 4 ≤ R ^ 4 := by gcongr; exact hsource x hw
    simpa only [planarFourthMomentIntegrand, norm_mul, Complex.norm_real, norm_pow,
      norm_star, LinearIsometryEquiv.norm_map] using
      mul_le_mul_of_nonneg_left hb (norm_nonneg (w x))

theorem integrable_planarFourthMomentIntegrand {w : R2 → ℝ} {R : ℝ}
    (hw : Integrable w) (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R) :
    Integrable (planarFourthMomentIntegrand w) := by
  have hp : Continuous (fun x : R2 => (star (complexPhysicalPlane.symm x)) ^ 4) :=
    (continuous_star.comp complexPhysicalPlane.symm.continuous).pow 4
  have hm : AEStronglyMeasurable (planarFourthMomentIntegrand w) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hw.aestronglyMeasurable).mul hp.aestronglyMeasurable
  exact (hw.norm.mul_const (R ^ 4)).mono' hm
    (ae_of_all _ (norm_planarFourthMomentIntegrand_le hsource))

theorem norm_planarFourthMoment_le {w : R2 → ℝ} {R : ℝ}
    (hw : Integrable w) (hsource : ∀ x, w x ≠ 0 → ‖x‖ ≤ R) :
    ‖planarFourthMoment w‖ ≤ (∫ x, ‖w x‖) * R ^ 4 := by
  unfold planarFourthMoment
  exact (norm_integral_le_of_norm_le (hw.norm.mul_const (R ^ 4))
    (ae_of_all _ (norm_planarFourthMomentIntegrand_le hsource))).trans_eq (integral_mul_const _ _)

theorem planarFourthMoment_sub {w f : R2 → ℝ} {R : ℝ}
    (hw : Integrable w) (hf : Integrable f)
    (hwR : ∀ x, w x ≠ 0 → ‖x‖ ≤ R) (hfR : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) :
    planarFourthMoment (w - f) = planarFourthMoment w - planarFourthMoment f := by
  unfold planarFourthMoment
  rw [← integral_sub (integrable_planarFourthMomentIntegrand hw hwR)
    (integrable_planarFourthMomentIntegrand hf hfR)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp only [planarFourthMomentIntegrand, Pi.sub_apply,
    Complex.ofReal_sub, sub_mul])

theorem norm_planarFourthMoment_sub_le {w f : R2 → ℝ} {R : ℝ}
    (hw : Integrable w) (hf : Integrable f)
    (hwR : ∀ x, w x ≠ 0 → ‖x‖ ≤ R) (hfR : ∀ x, f x ≠ 0 → ‖x‖ ≤ R) :
    ‖planarFourthMoment w - planarFourthMoment f‖ ≤ (∫ x, ‖w x - f x‖) * R ^ 4 := by
  rw [← planarFourthMoment_sub hw hf hwR hfR]
  apply norm_planarFourthMoment_le (hw.sub hf)
  intro x hx
  by_cases hz : w x = 0
  · apply hfR x
    intro hfz
    exact hx (by simp only [Pi.sub_apply, hz, hfz, sub_self])
  · exact hwR x hz

theorem tendsto_planarFourthMoment_of_L1
    {α : Type*} {l : Filter α} {w : α → R2 → ℝ} {w₀ : R2 → ℝ} {R : ℝ}
    (hw : ∀ a, Integrable (w a)) (hw₀ : Integrable w₀)
    (hsource : ∀ᶠ a in l, ∀ x, w a x ≠ 0 → ‖x‖ ≤ R)
    (hsource₀ : ∀ x, w₀ x ≠ 0 → ‖x‖ ≤ R)
    (hL : Tendsto (fun a => ∫ x, ‖w a x - w₀ x‖) l (𝓝 (0 : ℝ))) :
    Tendsto (fun a => planarFourthMoment (w a)) l (𝓝 (planarFourthMoment w₀)) := by
  have hb : ∀ᶠ a in l, ‖planarFourthMoment (w a) - planarFourthMoment w₀‖ ≤
      (∫ x, ‖w a x - w₀ x‖) * R ^ 4 := by
    filter_upwards [hsource] with a ha
    exact norm_planarFourthMoment_sub_le (hw a) hw₀ ha hsource₀
  have hz : Tendsto (fun a => planarFourthMoment (w a) - planarFourthMoment w₀) l (𝓝 (0 : ℂ)) :=
    squeeze_zero_norm' hb (by simpa only [zero_mul] using hL.mul_const (R ^ 4))
  simpa only [sub_add_cancel, zero_add] using hz.add_const (planarFourthMoment w₀)

end Euler2D

end
