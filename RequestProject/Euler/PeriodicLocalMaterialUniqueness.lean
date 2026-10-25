module

public import RequestProject.Euler.PeriodicLocalMaterialAffine
public import RequestProject.Euler.UniformLogLabelParticleUniqueness
public import RequestProject.Euler.LogFlowCompactness

/-! Weighted-active nonlinear uniqueness for the actual periodic local
singular kernel and the same genuine Lipschitz correction. -/

@[expose] public section
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal
namespace Euler2D

theorem periodicLocal_material_particle_uniqueness_active
    {w : R2 → ℝ} {T B C M : ℝ} {L : ℝ≥0} {A : Set R2}
    (hw : Integrable w μT) (hB0 : 0 ≤ B) (hB : ∀ᵐ b ∂μT, ‖w b‖ ≤ B)
    (hC : 0 ≤ C)
    (hderiv : ∀ z : R2, z ≠ 0 → ‖fderiv ℝ localPlanarKernel z‖ ≤ C * (‖z‖ ^ 2)⁻¹)
    (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hactive : ∀ᵐ b ∂μT, w b ≠ 0 → b ∈ A)
    (X Y vx vy : ℝ → R2 → R2) (E : ℝ → R2 → R2)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, TorusAreaPreserving (X t))
    (hY : ∀ t ∈ Icc (0 : ℝ) T, TorusAreaPreserving (Y t))
    (hE : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (E t))
    (hEb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖E t x‖ ≤ M)
    (hvc : ∀ a ∈ A, Continuous (fun t => vx t a))
    (hwc : ∀ a ∈ A, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a ∈ A, X 0 a = Y 0 a)
    (heqX : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vx t a = periodicLocalMaterialVelocity w (X t) (X t a) + E t (X t a))
    (heqY : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vy t a = periodicLocalMaterialVelocity w (Y t) (Y t a) + E t (Y t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, X t a = Y t a := by
  let V : ℝ := B * (∫ z in torusBox, ‖periodicLocalKernel z‖) + M
  let K : ℝ := periodicLocalCouplingCoefficient C * (B + ∫ b in torusBox, ‖w b‖) + (L : ℝ)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact add_nonneg (mul_nonneg (periodicLocalCouplingCoefficient_nonneg hC)
      (add_nonneg hB0 (integral_nonneg (fun _ => norm_nonneg _)))) L.coe_nonneg
  have hvX (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) : ‖vx t a‖ ≤ V := by
    rw [heqX t ht a ha]
    exact (norm_add_le _ _).trans (add_le_add (norm_periodicLocalMaterialVelocity_le hB (hX t ht) _) (hEb t ht _))
  have hvY (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) : ‖vy t a‖ ≤ V := by
    rw [heqY t ht a ha]
    exact (norm_add_le _ _).trans (add_le_add (norm_periodicLocalMaterialVelocity_le hB (hY t ht) _) (hEb t ht _))
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) : ‖X t a - X 0 a‖ ≤ V * t := by
    have hh := norm_trajectory_sub_time_le (v := fun s _ => vx s a)
      (fun s hs => hXd s hs a ha) (fun s hs _ => hvX s hs a ha)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT⟩) ht
    simpa only [sub_zero, abs_of_nonneg ht.1] using hh
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) : ‖Y t a - Y 0 a‖ ≤ V * t := by
    have hh := norm_trajectory_sub_time_le (v := fun s _ => vy s a)
      (fun s hs => hYd s hs a ha) (fun s hs _ => hvY s hs a ha)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT⟩) ht
    simpa only [sub_zero, abs_of_nonneg ht.1] using hh
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : A) : ‖X t a - Y t a‖ ≤ 2 * V * T := by
    calc
      _ ≤ ‖X t a - X 0 a‖ + ‖X 0 a - Y t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ V * t + V * t := add_le_add (hp t ht a a.property)
        (by rw [hinit a a.property, norm_sub_rev]; exact hq t ht a a.property)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hV]
  have he := uniform_log_label_particle_uniqueness (B := 2 * V * T) (C := K)
    (by positivity) hK (fun t (a : A) => X t a) (fun t (a : A) => Y t a)
    (fun t (a : A) => vx t a) (fun t (a : A) => vy t a)
    (fun a => hvc a a.property) (fun a => hwc a a.property)
    (fun t ht a => hXd t ht a a.property) (fun t ht a => hYd t ht a a.property)
    (fun a => hinit a a.property) hb ?_
  · intro t ht a ha
    exact he t ht ⟨a, ha⟩
  · intro t ht D hD hd a ε hε hε1
    have hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X t b - Y t b‖ ≤ D := by
      filter_upwards [hactive] with b hb hwb
      exact hd ⟨b, hb hwb⟩
    dsimp only
    rw [heqX t ht a a.property, heqY t ht a a.property]
    exact norm_periodicLocalMaterial_add_common_field_sub_le_affine hw hB0 hB hC hderiv
      (hX t ht) (hY t ht) hD (X t a) (Y t a) (hd a) hdist hε hε1 (hE t ht)

end Euler2D
end
