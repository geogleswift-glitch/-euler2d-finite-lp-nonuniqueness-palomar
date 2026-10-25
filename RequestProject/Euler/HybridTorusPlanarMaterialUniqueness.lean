module
public import RequestProject.Euler.HybridTorusPlanarMaterialAffine
public import RequestProject.Euler.UniformLogLabelParticleUniqueness

/-! Nonlinear uniqueness comparing genuine torus and plane material
trajectories, only on active initial labels. The kernel comparison is the
proved mixed singular estimate, not an assumed velocity modulus. -/
@[expose] public section
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal
namespace Euler2D

theorem hybrid_local_material_particle_uniqueness_active
    {w : R2 → ℝ} {T B H : ℝ} {L : ℝ≥0} {A : Set R2}
    (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0) (hH : 0 ≤ H)
    (hactive : ∀ᵐ b ∂μT, w b ≠ 0 → b ∈ A)
    (X Y vx vy : ℝ → R2 → R2) (E : ℝ → R2 → R2)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, TorusAreaPreserving (X t))
    (YH : Icc (0 : ℝ) T → R2 ≃ₜ R2)
    (hYH : ∀ t, (YH t : R2 → R2) = Y t)
    (hY : ∀ t, MeasurePreserving (YH t) volume volume)
    (hE : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (E t))
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      ∀ᵐ b ∂μT, w b ≠ 0 → ‖X t a - X t b‖ ≤ 1 / 2)
    (hvc : ∀ a ∈ A, Continuous (fun t => vx t a))
    (hwc : ∀ a ∈ A, Continuous (fun t => vy t a))
    (hXd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => X s a) (vx t a) t)
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a ∈ A, X 0 a = Y 0 a)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, ‖X t a - Y t a‖ ≤ H)
    (heqX : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vx t a = periodicLocalMaterialVelocity w (X t) (X t a) + E t (X t a))
    (heqY : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vy t a = planarMaterialLabelVelocity kernelK w (Y t) (Y t a) + E t (Y t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, X t a = Y t a := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let K : ℝ := hybridLocalCouplingCoefficient * (B + ∫ b in torusBox, ‖w b‖) + (L : ℝ)
  have hK : 0 ≤ K := add_nonneg (mul_nonneg hybridLocalCouplingCoefficient_nonneg
    (add_nonneg hB0 (integral_nonneg (fun _ => norm_nonneg _)))) L.coe_nonneg
  have he := uniform_log_label_particle_uniqueness hH hK
    (fun t (a : A) => X t a) (fun t (a : A) => Y t a)
    (fun t (a : A) => vx t a) (fun t (a : A) => vy t a)
    (fun a => hvc a a.property) (fun a => hwc a a.property)
    (fun t ht a => hXd t ht a a.property) (fun t ht a => hYd t ht a a.property)
    (fun a => hinit a a.property) (fun t ht a => hbound t ht a a.property) ?_
  · intro t ht a ha
    exact he t ht ⟨a, ha⟩
  · intro t ht D hD hd a ε hε hε1
    have hdist : ∀ᵐ b ∂μT, w b ≠ 0 → ‖X t b - YH ⟨t, ht⟩ b‖ ≤ D := by
      rw [hYH]
      filter_upwards [hactive] with b hb hwb
      exact hd ⟨b, hb hwb⟩
    dsimp only
    rw [heqX t ht a a.property, heqY t ht a a.property]
    have hh := norm_hybrid_material_add_common_field_sub_le_affine hw hB hwzero
      (hX t ht) (YH ⟨t, ht⟩) (hY ⟨t, ht⟩) hD (X t a) (Y t a) (hd a)
      (hsmall t ht a a.property) hdist hε hε1 (hE t ht)
    rw [hYH] at hh
    exact hh

end Euler2D
end
