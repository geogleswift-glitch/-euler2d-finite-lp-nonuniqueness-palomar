module

public import RequestProject.Euler.SmoothFlowVariational
public import RequestProject.Euler.SmoothFlowTaylor

/-!
# The actual spatial derivative of the particle flow

Uniform Taylor estimates and Grönwall's inequality identify the genuine
Fréchet derivative with the genuinely constructed variational solution.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

lemma gronwallBound_zero_smul (K c t : ℝ) :
    gronwallBound 0 K c t = c * gronwallBound 0 K 1 t := by
  unfold gronwallBound
  split_ifs <;> ring

theorem particleForward_linearization_small {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (a : R2) {A : ℝ → R2 →L[ℝ] R2} (hAc : Continuous A)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ R2)
    (hAd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt A
      ((fderiv ℝ (v u) (boundedParticleForward hv hT u a)).comp (A u)) u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : R2, ‖h‖ ≤ δ →
      ‖flowLinearizationError hv hT ⟨0, le_rfl, hT⟩ a h A t‖ ≤ ε * ‖h‖ := by
  let E : ℝ := Real.exp ((K : ℝ) * T)
  let C : ℝ := |gronwallBound 0 (K : ℝ) 1 t| + 1
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 < C := by dsimp [C]; positivity
  let η : ℝ := ε / (E * C)
  have hη : 0 < η := div_pos hε (mul_pos hE hC)
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_spatialTaylor_remainder hC1
    (boundedParticleFlow_continuous_time hv hT ⟨0, le_rfl, hT⟩ a) hT hη
  refine ⟨δ / E, div_pos hδ hE, ?_⟩
  intro h hh
  let B : ℝ → R2 →L[ℝ] R2 := fun u => fderiv ℝ (v u) (boundedParticleForward hv hT u a)
  have hdisp (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      ‖particleDisplacement hv hT ⟨0, le_rfl, hT⟩ a h u‖ ≤ E * ‖h‖ := by
    have hd := boundedParticleFlow_dist_le hv hT ⟨0, le_rfl, hT⟩ ⟨u, hu⟩ (a + h) a
    have hdu : ‖particleDisplacement hv hT ⟨0, le_rfl, hT⟩ a h u‖ ≤
        ‖h‖ * Real.exp ((K : ℝ) * u) := by
      simpa only [particleDisplacement, dist_eq_norm, add_sub_cancel_left, sub_zero,
        abs_of_nonneg hu.1] using hd
    exact hdu.trans (by
      rw [mul_comm E]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hu.2 K.2)) (norm_nonneg h))
  have hrem (u : ℝ) (hu : u ∈ Ico (0 : ℝ) t) :
      ‖flowVelocityRemainder hv hT ⟨0, le_rfl, hT⟩ a h B u‖ ≤ η * E * ‖h‖ := by
    have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.le.trans ht.2⟩
    have hsmall : ‖particleDisplacement hv hT ⟨0, le_rfl, hT⟩ a h u‖ ≤ δ :=
      (hdisp u huT).trans (by simpa only [mul_comm] using (le_div_iff₀ hE).mp hh)
    have hTayloru := hTaylor u huT (particleDisplacement hv hT ⟨0, le_rfl, hT⟩ a h u) hsmall
    have heq : boundedParticleFlow hv hT ⟨0, le_rfl, hT⟩ u a +
        particleDisplacement hv hT ⟨0, le_rfl, hT⟩ a h u =
        boundedParticleFlow hv hT ⟨0, le_rfl, hT⟩ u (a + h) := by
      simp only [particleDisplacement]
      abel
    have hr : ‖flowVelocityRemainder hv hT ⟨0, le_rfl, hT⟩ a h B u‖ ≤
        η * ‖particleDisplacement hv hT ⟨0, le_rfl, hT⟩ a h u‖ := by
      simpa only [flowVelocityRemainder, B, boundedParticleForward, heq] using hTayloru
    exact hr.trans (by nlinarith [hdisp u huT])
  have herr := norm_flowLinearizationError_le hv hT ⟨0, le_rfl, hT⟩ ⟨t, ht⟩ ht.1 a h
    hAc hA0 (fun u hu => hAd u ⟨hu.1, hu.2.le.trans ht.2⟩)
    (fun u hu => norm_spatialVelocityDerivative_le hv u _) hrem
  have hcoeff : gronwallBound 0 (K : ℝ) 1 t ≤ C :=
    (le_abs_self _).trans (by dsimp [C]; linarith [abs_nonneg (gronwallBound 0 (K : ℝ) 1 t)])
  calc
    ‖flowLinearizationError hv hT ⟨0, le_rfl, hT⟩ a h A t‖ ≤
        gronwallBound 0 K (η * E * ‖h‖) t := by simpa only [sub_zero] using herr
    _ = (η * E * ‖h‖) * gronwallBound 0 (K : ℝ) 1 t := gronwallBound_zero_smul _ _ _
    _ ≤ (η * E * ‖h‖) * C := mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = ε * ‖h‖ := by dsimp [η]; field_simp

theorem hasFDerivAt_particleForward_of_variational {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T)
    (a : R2) {A : ℝ → R2 →L[ℝ] R2} (hAc : Continuous A)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ R2)
    (hAd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt A
      ((fderiv ℝ (v u) (boundedParticleForward hv hT u a)).comp (A u)) u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (boundedParticleForward hv hT t) (A t) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, herror⟩ := particleForward_linearization_small hv hC1 hT a hAc hA0 hAd ht hε
  filter_upwards [ball_mem_nhds (0 : R2) hδ] with h hh
  exact herror h (show ‖h‖ < δ by simpa only [mem_ball, dist_zero_right] using hh).le

/-- A variational solution exists, and is the actual Fréchet derivative
of the previously constructed particle flow. -/
theorem exists_particleForward_spatial_derivative {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : ContDiff ℝ 1 (Function.uncurry v)) {T : ℝ} (hT : 0 ≤ T) (a : R2) :
    ∃ A : ℝ → R2 →L[ℝ] R2, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ R2 ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A
        ((fderiv ℝ (v t) (boundedParticleForward hv hT t a)).comp (A t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasFDerivAt (boundedParticleForward hv hT t) (A t) a := by
  have hBc : Continuous (fun t => fderiv ℝ (v t) (boundedParticleForward hv hT t a)) :=
    Continuous.fderiv_one hC1 (boundedParticleFlow_continuous_time hv hT ⟨0, le_rfl, hT⟩ a)
  obtain ⟨A, hAc, hA0, hAd, hAn⟩ := exists_variational_curve hBc
    (fun t => norm_spatialVelocityDerivative_le hv t _) hT
  exact ⟨A, hAc, hA0, hAd, fun t ht =>
    hasFDerivAt_particleForward_of_variational hv hC1 hT a hAc hA0 hAd ht⟩

end Euler2D

end
