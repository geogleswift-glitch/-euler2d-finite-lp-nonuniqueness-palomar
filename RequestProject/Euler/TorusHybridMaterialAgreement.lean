module
public import RequestProject.Euler.TorusParticleMaterialVelocity
public import RequestProject.Euler.BoundedEulerGeometry
public import RequestProject.Euler.HybridTorusPlanarMaterialUniqueness

/-! Identification of the same actual torus Euler system with a genuine
plane material flow driven by its own planar vorticity and the correction
of that torus system. Periodic and boxed initial representatives are
compared only through the actual box measure. -/
@[expose] public section
set_option maxHeartbeats 2500000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal
namespace Euler2D
namespace BoundedEulerParticleSystem
variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_lipschitzWith_correctionLabelField :
    ∃ L : ℝ≥0, ∀ t : ℝ, LipschitzWith L (S.correctionLabelField t) := by
  obtain ⟨C, _, _, hC⟩ := exists_torusGreenCorrection_perpGradient_bounds
  let m : ℝ≥0 := ⟨∫ b in torusBox, ‖f b‖, integral_nonneg (fun _ => norm_nonneg _)⟩
  have hw : Integrable (fun b => ‖f b‖) μT := ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)).norm
  refine ⟨C * m, fun t => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  unfold correctionLabelField
  rw [← integral_sub (S.integrable_correctionLabelField_integrand t x) (S.integrable_correctionLabelField_integrand t y)]
  calc
    _ ≤ ∫ b in torusBox, ‖f b‖ * ((C : ℝ) * ‖x - y‖) := by
      apply norm_integral_le_of_norm_le (hw.mul_const _)
      exact ae_of_all _ fun b => by
        rw [← smul_sub, norm_smul]
        have he := hC.dist_le_mul (x - S.forward t b + torusCenter) (y - S.forward t b + torusCenter)
        rw [dist_eq_norm, dist_eq_norm] at he
        have ha : (x - S.forward t b + torusCenter) - (y - S.forward t b + torusCenter) = x - y := by abel
        rw [ha] at he
        exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; simp only [NNReal.coe_mul, m, NNReal.coe_mk, dist_eq_norm]; ring

theorem particleVelocityRepresentative_eq_boxed_localMaterial_add_correction
    {w v : R2 → ℝ} {B : ℝ}
    (hwv : w =ᵐ[μT] v) (hvf : v =ᵐ[μT] (f : R2 → ℝ)) (hvper : IsTorusPeriodic v)
    (hB : ∀ b, ‖w b‖ ≤ B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    particleVelocityRepresentative f S.backward S.backward_area t x =
      periodicLocalMaterialVelocity w (S.forward t) x + S.correctionLabelField t x := by
  have hBv : ∀ᵐ b ∂μT, ‖v b‖ ≤ B := by
    filter_upwards [hwv] with b hb
    rw [← hb]
    exact hB b
  rw [S.particleVelocityRepresentative_eq_localMaterial_add_correction hvf hvper hBv ht x]
  congr 1
  unfold periodicLocalMaterialVelocity
  apply integral_congr_ae
  filter_upwards [hwv] with b hb
  rw [hb]

theorem forward_eq_plane_material_active
    {w v : R2 → ℝ} {B H : ℝ} {A : Set R2}
    (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    (hwv : w =ᵐ[μT] v) (hvf : v =ᵐ[μT] (f : R2 → ℝ)) (hvper : IsTorusPeriodic v)
    (hH : 0 ≤ H) (hactive : ∀ᵐ b ∂μT, w b ≠ 0 → b ∈ A)
    (Y vy : ℝ → R2 → R2)
    (YH : Icc (0 : ℝ) T → R2 ≃ₜ R2)
    (hYH : ∀ t, (YH t : R2 → R2) = Y t)
    (hY : ∀ t, MeasurePreserving (YH t) volume volume)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      ∀ᵐ b ∂μT, w b ≠ 0 → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2)
    (hyc : ∀ a ∈ A, Continuous (fun t => vy t a))
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a ∈ A, Y 0 a = a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ‖S.forward t a - Y t a‖ ≤ H)
    (heqY : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vy t a = planarMaterialLabelVelocity kernelK w (Y t) (Y t a) + S.correctionLabelField t (Y t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, S.forward t a = Y t a := by
  obtain ⟨L, hL⟩ := S.exists_lipschitzWith_correctionLabelField
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hBf : ∀ᵐ b ∂μT, ‖f b‖ ≤ B := by
    filter_upwards [hwv.trans hvf] with b hb
    rw [← hb]
    exact hB b
  let V : ℝ → R2 → R2 := particleVelocityRepresentative f S.backward S.backward_area
  let vx : ℝ → R2 → R2 := fun t a => V t (S.forward t a)
  have hVc : Continuous (Function.uncurry V) :=
    continuous_particleVelocityRepresentative f hB0 hBf S.backward_area S.backward_continuous
  have hvc (a : R2) : Continuous (fun t => vx t a) := by
    let j : ℝ → ℝ × R2 := fun t => (t, S.forward t a)
    have hj : Continuous j := continuous_id.prodMk
      (S.forward_continuous.comp (continuous_id.prodMk continuous_const))
    exact hVc.comp (f := j) hj
  apply hybrid_local_material_particle_uniqueness_active hw hB hwzero hH hactive
    S.forward Y vx vy S.correctionLabelField S.forward_area YH hYH hY
    (fun t _ => hL t) hsmall (fun a _ => hvc a) hyc
    (fun t ht a _ => S.derivative t ht a) hYd
    (fun a ha => (S.initial a).trans (hinit a ha).symm) hbound ?_ heqY
  intro t ht a ha
  exact S.particleVelocityRepresentative_eq_boxed_localMaterial_add_correction hwv hvf hvper hB ht (S.forward t a)

end BoundedEulerParticleSystem
end Euler2D
end
