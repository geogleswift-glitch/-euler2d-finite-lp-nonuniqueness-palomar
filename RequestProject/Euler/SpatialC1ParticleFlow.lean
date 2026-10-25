module

public import RequestProject.Euler.SmoothFlowVolume

/-!
# Volume preservation with only continuous time dependence

The spatial derivative is jointly continuous and exists at every space point.
No time derivative of the velocity is required. All particle trajectories,
variational solutions, spatial derivatives and volume identities are the
actual constructions from the preceding modules.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

structure IsC1SpatialVelocity (v : ℝ → R2 → R2) : Prop where
  differentiable : ∀ t, Differentiable ℝ (v t)
  continuous_fderiv : Continuous (fun p : ℝ × R2 => fderiv ℝ (v p.1) p.2)

lemma IsC1SpatialVelocity.of_contDiff {v : ℝ → R2 → R2}
    (hv : ContDiff ℝ 1 (Function.uncurry v)) : IsC1SpatialVelocity v where
  differentiable _t := (hv.comp (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero
  continuous_fderiv := continuous_spatialVelocityDerivative hv

theorem uniform_spatialTaylor_remainder_of_spatialC1 {v : ℝ → R2 → R2}
    (hv : IsC1SpatialVelocity v) {x : ℝ → R2} (hx : Continuous x)
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) T, ∀ d : R2, ‖d‖ ≤ δ →
      ‖v t (x t + d) - v t (x t) - fderiv ℝ (v t) (x t) d‖ ≤ ε * ‖d‖ := by
  let D : ℝ × R2 → R2 →L[ℝ] R2 := fun p => fderiv ℝ (v p.1) p.2
  have hDc : Continuous D := hv.continuous_fderiv
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx.continuousOn
    (s := Icc (0 : ℝ) T)
  have hC0 : 0 ≤ C := (norm_nonneg (x 0)).trans (hC 0 ⟨le_rfl, hT⟩)
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ closedBall (0 : R2) (C + 1)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨η, hη, hηD⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hDc.continuousOn) ε hε
  let δ : ℝ := min 1 (η / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (half_pos hη)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ < η := (min_le_right _ _).trans_lt (half_lt_self hη)
  refine ⟨δ, hδ, ?_⟩
  intro t ht d hd
  have hbase : (t, x t) ∈ Icc (0 : ℝ) T ×ˢ closedBall (0 : R2) (C + 1) :=
    ⟨ht, by simpa only [mem_closedBall, dist_zero_right] using (hC t ht).trans (by linarith : C ≤ C + 1)⟩
  have hnear (y : R2) (hy : y ∈ closedBall (x t) δ) :
      ‖D (t, y) - D (t, x t)‖ ≤ ε := by
    have hnorm : ‖y‖ ≤ C + 1 := by
      calc
        ‖y‖ ≤ ‖y - x t‖ + ‖x t‖ := by simpa only [add_comm] using norm_le_insert' y (x t)
        _ ≤ δ + C := add_le_add (mem_closedBall_iff_norm.mp hy) (hC t ht)
        _ ≤ C + 1 := by linarith
    have hs : (t, y) ∈ Icc (0 : ℝ) T ×ˢ closedBall (0 : R2) (C + 1) :=
      ⟨ht, by simpa only [mem_closedBall, dist_zero_right] using hnorm⟩
    have hdist : dist (t, y) (t, x t) < η := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using
        (mem_closedBall.mp hy).trans_lt hδη
    simpa only [dist_eq_norm] using (hηD (t, y) hs (t, x t) hbase hdist).le
  let g : R2 → R2 := fun y => v t y - D (t, x t) y
  have hvg : Differentiable ℝ (v t) :=
    hv.differentiable t
  have hgd (y : R2) : HasFDerivAt g (D (t, y) - D (t, x t)) y :=
    (hvg y).hasFDerivAt.sub (D (t, x t)).hasFDerivAt
  have hm := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => (hgd y).hasFDerivWithinAt) hnear (convex_closedBall (x t) δ)
    (mem_closedBall_self hδ.le) (show x t + d ∈ closedBall (x t) δ by
      simpa only [mem_closedBall_iff_norm, add_sub_cancel_left] using hd)
  have heq : g (x t + d) - g (x t) =
      v t (x t + d) - v t (x t) - D (t, x t) d := by
    simp only [g, map_add]
    abel
  simpa only [heq, add_sub_cancel_left] using hm

theorem particleForward_linearization_small_of_spatialC1 {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : IsC1SpatialVelocity v) {T : ℝ} (hT : 0 ≤ T)
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
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_spatialTaylor_remainder_of_spatialC1 hC1
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

theorem hasFDerivAt_particleForward_of_variational_spatialC1 {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : IsC1SpatialVelocity v) {T : ℝ} (hT : 0 ≤ T)
    (a : R2) {A : ℝ → R2 →L[ℝ] R2} (hAc : Continuous A)
    (hA0 : A 0 = ContinuousLinearMap.id ℝ R2)
    (hAd : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt A
      ((fderiv ℝ (v u) (boundedParticleForward hv hT u a)).comp (A u)) u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasFDerivAt (boundedParticleForward hv hT t) (A t) a := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, herror⟩ := particleForward_linearization_small_of_spatialC1 hv hC1 hT a hAc hA0 hAd ht hε
  filter_upwards [ball_mem_nhds (0 : R2) hδ] with h hh
  exact herror h (show ‖h‖ < δ by simpa only [mem_ball, dist_zero_right] using hh).le

/-- A variational solution exists, and is the actual Fréchet derivative
of the previously constructed particle flow. -/
theorem exists_particleForward_spatial_derivative_of_spatialC1 {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : IsC1SpatialVelocity v) {T : ℝ} (hT : 0 ≤ T) (a : R2) :
    ∃ A : ℝ → R2 →L[ℝ] R2, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ R2 ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A
        ((fderiv ℝ (v t) (boundedParticleForward hv hT t a)).comp (A t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasFDerivAt (boundedParticleForward hv hT t) (A t) a := by
  have hBc : Continuous (fun t => fderiv ℝ (v t) (boundedParticleForward hv hT t a)) :=
    hC1.continuous_fderiv.comp (continuous_id.prodMk
      (boundedParticleFlow_continuous_time hv hT ⟨0, le_rfl, hT⟩ a))
  obtain ⟨A, hAc, hA0, hAd, hAn⟩ := exists_variational_curve hBc
    (fun t => norm_spatialVelocityDerivative_le hv t _) hT
  exact ⟨A, hAc, hA0, hAd, fun t ht =>
    hasFDerivAt_particleForward_of_variational_spatialC1 hv hC1 hT a hAc hA0 hAd ht⟩

theorem det_fderiv_boundedParticleForward_of_spatialC1 {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : IsC1SpatialVelocity v) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
    (fderiv ℝ (boundedParticleForward hv hT t) a).det = 1 := by
  obtain ⟨A, hAc, hA0, hAd, hAf⟩ := exists_particleForward_spatial_derivative_of_spatialC1 hv hC1 hT a
  rw [(hAf t ht).fderiv, ← linearDet2_eq_det]
  exact linearDet2_variational_eq_one hT hA0 hAd
    (fun u hu => hdiv u (boundedParticleForward hv hT u a)) ht

theorem measurePreserving_boundedParticleForward_of_spatialC1 {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : IsC1SpatialVelocity v) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MeasurePreserving (boundedParticleForward hv hT t) volume volume := by
  let X := boundedParticleHomeomorph hv hT ⟨0, le_rfl, hT⟩ ⟨t, ht⟩
  have hX : (X : R2 → R2) = boundedParticleForward hv hT t := rfl
  have hdiff (a : R2) : DifferentiableAt ℝ (boundedParticleForward hv hT t) a := by
    obtain ⟨A, hAc, hA0, hAd, hAf⟩ := exists_particleForward_spatial_derivative_of_spatialC1 hv hC1 hT a
    exact (hAf t ht).differentiableAt
  have hXm : Measurable (boundedParticleForward hv hT t) := by
    rw [← hX]; exact X.continuous.measurable
  refine ⟨hXm, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hXm hs]
  have hp : MeasurableSet ((boundedParticleForward hv hT t) ⁻¹' s) :=
    hXm hs
  have himage : (boundedParticleForward hv hT t) '' ((boundedParticleForward hv hT t) ⁻¹' s) = s :=
    Set.image_preimage_eq s (by rw [← hX]; exact X.surjective)
  have hj := lintegral_abs_det_fderiv_eq_addHaar_image volume hp
    (fun a ha => (hdiff a).hasFDerivAt.hasFDerivWithinAt)
    (by rw [← hX]; exact X.injective.injOn)
  simpa only [det_fderiv_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv ht, abs_one,
    ENNReal.ofReal_one, lintegral_one, Measure.restrict_apply_univ, himage] using hj

theorem measurePreserving_boundedParticleBackward_of_spatialC1 {v : ℝ → R2 → R2} {K M : ℝ≥0}
    (hv : IsBoundedLipschitzVelocity v K M)
    (hC1 : IsC1SpatialVelocity v) {T : ℝ} (hT : 0 ≤ T)
    (hdiv : ∀ t x, pd 0 (v t) x 0 + pd 1 (v t) x 1 = 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    MeasurePreserving (boundedParticleBackward hv hT t) volume volume := by
  let X := boundedParticleHomeomorph hv hT ⟨0, le_rfl, hT⟩ ⟨t, ht⟩
  have hXm : MeasurePreserving (X : R2 → R2) volume volume :=
    measurePreserving_boundedParticleForward_of_spatialC1 hv hC1 hT hdiv ht
  have heq : boundedParticleBackward hv hT t = (X.symm : R2 → R2) := by
    funext a
    simp only [boundedParticleBackward, projIcc_of_mem _ ht]
    rfl
  rw [heq]
  refine ⟨X.symm.continuous.measurable, ?_⟩
  calc
    Measure.map (X.symm : R2 → R2) volume =
        Measure.map (X.symm : R2 → R2) (Measure.map (X : R2 → R2) volume) :=
      congrArg (Measure.map (X.symm : R2 → R2)) hXm.map_eq.symm
    _ = Measure.map ((X.symm : R2 → R2) ∘ X) volume :=
      Measure.map_map X.symm.continuous.measurable X.continuous.measurable
    _ = volume := by
      have hc : (X.symm : R2 → R2) ∘ X = id := by funext a; exact X.symm_apply_apply a
      rw [hc, Measure.map_id]

end Euler2D

end
