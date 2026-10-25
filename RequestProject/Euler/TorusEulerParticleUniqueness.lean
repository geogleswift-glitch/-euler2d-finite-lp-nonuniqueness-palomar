module
public import RequestProject.Euler.TorusParticleMaterialVelocity
public import RequestProject.Euler.BoundedEulerGeometry
public import RequestProject.Euler.PeriodicLocalMaterialAffine
public import RequestProject.Euler.UniformLogLabelParticleUniqueness

/-! Self-consistent uniqueness for the actual original torus Euler
particle systems. Both the singular local term and the change in the
actual Green correction are controlled from their true label integrals. -/
@[expose] public section
set_option maxHeartbeats 2500000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal
namespace Euler2D
namespace BoundedEulerParticleSystem
variable {f : Lp ℝ 2 μT} {T : ℝ} (S Q : BoundedEulerParticleSystem f T)

theorem norm_correctionLabelField_sub_le {C : ℝ≥0} {D : ℝ}
    (hC : LipschitzWith C (perpGradient torusGreenCorrection))
    (hD : 0 ≤ D) (t : ℝ) (x y : R2)
    (hdist : ∀ b, ‖S.forward t b - Q.forward t b‖ ≤ D) :
    ‖S.correctionLabelField t x - Q.correctionLabelField t y‖ ≤
      ((C : ℝ) * ∫ b in torusBox, ‖f b‖) * (‖x - y‖ + D) := by
  have hw : Integrable (fun b => ‖f b‖) μT := ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)).norm
  unfold correctionLabelField
  rw [← integral_sub (S.integrable_correctionLabelField_integrand t x)
    (Q.integrable_correctionLabelField_integrand t y)]
  calc
    _ ≤ ∫ b in torusBox, ‖f b‖ * ((C : ℝ) * (‖x - y‖ + D)) := by
      apply norm_integral_le_of_norm_le (hw.mul_const _)
      exact ae_of_all _ fun b => by
        rw [← smul_sub, norm_smul]
        have ha : (x - S.forward t b + torusCenter) - (y - Q.forward t b + torusCenter) =
            (x - y) - (S.forward t b - Q.forward t b) := by abel
        have hn : ‖(x - S.forward t b + torusCenter) - (y - Q.forward t b + torusCenter)‖ ≤ ‖x - y‖ + D := by
          rw [ha]
          exact (norm_sub_le _ _).trans (add_le_add_right (hdist b) _)
        have he := hC.dist_le_mul (x - S.forward t b + torusCenter) (y - Q.forward t b + torusCenter)
        rw [dist_eq_norm, dist_eq_norm] at he
        exact mul_le_mul_of_nonneg_left (he.trans (mul_le_mul_of_nonneg_left hn C.coe_nonneg)) (norm_nonneg _)
    _ = _ := by rw [integral_mul_const]; ring

theorem forward_eq_of_bounded_vorticity
    {v : R2 → ℝ} {B : ℝ} (hvf : v =ᵐ[μT] (f : R2 → ℝ))
    (hvper : IsTorusPeriodic v) (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖v b‖ ≤ B) (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, S.forward t a = Q.forward t a := by
  have hw : Integrable v μT := ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)).congr hvf.symm
  have hBf : ∀ᵐ b ∂μT, ‖f b‖ ≤ B := by
    filter_upwards [hvf, hB] with b hb hn
    rw [← hb]
    exact hn
  obtain ⟨C, hC, hderiv⟩ := exists_norm_fderiv_localPlanarKernel_le
  obtain ⟨G, _, _, hG⟩ := exists_torusGreenCorrection_perpGradient_bounds
  let A : ℝ := ∫ b in torusBox, ‖v b‖
  let m : ℝ := ∫ b in torusBox, ‖f b‖
  let V : ℝ := B * ∫ z in torusBox, ‖torusBiotSavartKernel z‖
  let K : ℝ := periodicLocalCouplingCoefficient C * (B + A) + 2 * (G : ℝ) * m
  have hA : 0 ≤ A := integral_nonneg (fun _ => norm_nonneg _)
  have hm : 0 ≤ m := integral_nonneg (fun _ => norm_nonneg _)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg (mul_nonneg (periodicLocalCouplingCoefficient_nonneg hC.le) (add_nonneg hB0 hA)) (by positivity)
  let vx : ℝ → R2 → R2 := fun t a => particleVelocityRepresentative f S.backward S.backward_area t (S.forward t a)
  let vy : ℝ → R2 → R2 := fun t a => particleVelocityRepresentative f Q.backward Q.backward_area t (Q.forward t a)
  have hvc (a : R2) : Continuous (fun t => vx t a) := by
    let j : ℝ → ℝ × R2 := fun t => (t, S.forward t a)
    have hj : Continuous j := continuous_id.prodMk (S.forward_continuous.comp (continuous_id.prodMk continuous_const))
    exact (continuous_particleVelocityRepresentative f hB0 hBf S.backward_area S.backward_continuous).comp (f := j) hj
  have hwc (a : R2) : Continuous (fun t => vy t a) := by
    let j : ℝ → ℝ × R2 := fun t => (t, Q.forward t a)
    have hj : Continuous j := continuous_id.prodMk (Q.forward_continuous.comp (continuous_id.prodMk continuous_const))
    exact (continuous_particleVelocityRepresentative f hB0 hBf Q.backward_area Q.backward_continuous).comp (f := j) hj
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) : ‖S.forward t a - Q.forward t a‖ ≤ 2 * V * T := by
    calc
      _ ≤ ‖S.forward t a - a‖ + ‖a - Q.forward t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ V * t + V * t := add_le_add (S.displacement_le hT hBf ht a)
        (by rw [norm_sub_rev]; exact Q.displacement_le hT hBf ht a)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hV]
  apply uniform_log_label_particle_uniqueness (B := 2 * V * T) (C := K)
    (by positivity) hK S.forward Q.forward vx vy hvc hwc S.derivative Q.derivative
    (fun a => (S.initial a).trans (Q.initial a).symm) hb
  intro t ht D hD hd a ε hε hε1
  dsimp only [vx, vy]
  rw [S.particleVelocityRepresentative_eq_localMaterial_add_correction hvf hvper hB ht,
    Q.particleVelocityRepresentative_eq_localMaterial_add_correction hvf hvper hB ht]
  have hdist : ∀ᵐ b ∂μT, v b ≠ 0 → ‖S.forward t b - Q.forward t b‖ ≤ D :=
    ae_of_all _ (fun b _ => hd b)
  have hl := norm_periodicLocalMaterial_sub_le_epsilon_affine hw hB0 hB hC.le hderiv
    (S.forward_area t ht) (Q.forward_area t ht) hD (S.forward t a) (Q.forward t a) (hd a) hdist hε hε1
  have hg := S.norm_correctionLabelField_sub_le Q hG hD t (S.forward t a) (Q.forward t a) hd
  have hg' : ‖S.correctionLabelField t (S.forward t a) - Q.correctionLabelField t (Q.forward t a)‖ ≤ 2 * (G : ℝ) * m * D := by
    have hh := mul_le_mul_of_nonneg_left (hd a) (show 0 ≤ (G : ℝ) * m by positivity)
    dsimp only [m] at *
    nlinarith
  have hlog : 1 ≤ 1 - Real.log ε := by linarith [Real.log_nonpos hε.le hε1]
  have heps : D ≤ (1 - Real.log ε) * D + ε := by nlinarith
  have hgreen := mul_le_mul_of_nonneg_left heps (show 0 ≤ 2 * (G : ℝ) * m by positivity)
  rw [add_sub_add_comm]
  have hh := (norm_add_le _ _).trans (add_le_add hl hg')
  dsimp only [K, A]
  nlinarith

theorem backward_eq_of_bounded_vorticity
    {v : R2 → ℝ} {B : ℝ} (hvf : v =ᵐ[μT] (f : R2 → ℝ))
    (hvper : IsTorusPeriodic v) (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖v b‖ ≤ B) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) : S.backward t x = Q.backward t x := by
  have he := S.forward_eq_of_bounded_vorticity Q hvf hvper hB0 hB hT t ht (Q.backward t x)
  rw [Q.forward_backward t ht x] at he
  have hh := congrArg (S.backward t) he
  rw [S.backward_forward t ht] at hh
  exact hh.symm


theorem forward_eq_of_ae_bounded_initial
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖f b‖ ≤ B) (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a, S.forward t a = Q.forward t a := by
  have hvf := torusExtension_ae (f : R2 → ℝ)
  have hvB : ∀ᵐ b ∂μT, ‖torusExtension (f : R2 → ℝ) b‖ ≤ B := by
    filter_upwards [hvf, hB] with b hb hn
    rw [hb]
    exact hn
  exact S.forward_eq_of_bounded_vorticity Q hvf (isTorusPeriodic_torusExtension _) hB0 hvB hT

theorem backward_eq_of_ae_bounded_initial
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖f b‖ ≤ B) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) : S.backward t x = Q.backward t x := by
  have he := S.forward_eq_of_ae_bounded_initial Q hB0 hB hT t ht (Q.backward t x)
  rw [Q.forward_backward t ht x] at he
  have hh := congrArg (S.backward t) he
  rw [S.backward_forward t ht] at hh
  exact hh.symm

theorem velocity_eq_of_ae_bounded_initial
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖f b‖ ≤ B) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    particleVelocityRepresentative f S.backward S.backward_area t x =
      particleVelocityRepresentative f Q.backward Q.backward_area t x := by
  have hvf := torusExtension_ae (f : R2 → ℝ)
  have hvB : ∀ᵐ b ∂μT, ‖torusExtension (f : R2 → ℝ) b‖ ≤ B := by
    filter_upwards [hvf, hB] with b hb hn
    rw [hb]
    exact hn
  rw [S.particleVelocityRepresentative_eq_material hvf (isTorusPeriodic_torusExtension _) hvB ht x,
    Q.particleVelocityRepresentative_eq_material hvf (isTorusPeriodic_torusExtension _) hvB ht x]
  apply integral_congr_ae
  exact ae_of_all _ fun b => by dsimp only; rw [S.forward_eq_of_ae_bounded_initial Q hB0 hB hT t ht b]

theorem vorticity_eq_of_ae_bounded_initial
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖f b‖ ≤ B) (hT : 0 ≤ T)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    particleCurlL2 f S.backward S.backward_area t = particleCurlL2 f Q.backward Q.backward_area t := by
  apply Lp.ext
  filter_upwards [particleCurlL2_ae f S.backward S.backward_area t,
    particleCurlL2_ae f Q.backward Q.backward_area t] with x hx hy
  rw [hx, hy, S.backward_eq_of_ae_bounded_initial Q hB0 hB hT t ht x]
end BoundedEulerParticleSystem
end Euler2D
end
