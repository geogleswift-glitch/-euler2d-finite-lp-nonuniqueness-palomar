module

public import RequestProject.Euler.TorusPartialMaterialVelocity
public import RequestProject.Euler.HybridTorusPlanarLogMaterialUniqueness

/-! Identification with the original Euler particles when only a finite
active part of the initial density is represented by material contours.
The complementary density remains transported by the same Euler system. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem forward_eq_plane_partial_material_active_of_velocity_bounds
    {w v q : R2 → ℝ} {B M : ℝ} {A : Set R2}
    (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    (hwv : w =ᵐ[μT] v) (hvper : IsTorusPeriodic v)
    (hq : MemLp q 2 μT) (hqper : IsTorusPeriodic q) (hM : ∀ b, ‖q b‖ ≤ M)
    (hvf : (fun b => v b + q b) =ᵐ[μT] (f : R2 → ℝ))
    (hT : 0 ≤ T) (hactive : ∀ᵐ b ∂μT, w b ≠ 0 → b ∈ A)
    (Y vy : ℝ → R2 → R2)
    (YH : Icc (0 : ℝ) T → R2 ≃ₜ R2)
    (hYH : ∀ t, (YH t : R2 → R2) = Y t)
    (hY : ∀ t, MeasurePreserving (YH t) volume volume)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      ∀ᵐ b ∂μT, w b ≠ 0 → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2)
    (hinnerSmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      ∀ᵐ y ∂μT, S.transportedScalar q t y ≠ 0 → ‖S.forward t a - y‖ ≤ 1 / 2)
    (hyc : ∀ a ∈ A, Continuous (fun t => vy t a))
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a ∈ A, Y 0 a = a)
    (heqY : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vy t a = planarMaterialLabelVelocity kernelK w (Y t) (Y t a) +
        S.physicalLabelCommonField q t (Y t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, S.forward t a = Y t a := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hqint : Integrable q μT := hq.integrable (by norm_num)
  have hvint : Integrable v μT :=
    (hw.mono_measure Measure.restrict_le_self).congr hwv
  have hBv : ∀ᵐ b ∂μT, ‖v b‖ ≤ B := by
    filter_upwards [hwv] with b hb
    rw [← hb]
    exact hB b
  have hBq : ∀ᵐ b ∂μT, ‖q b‖ ≤ M := ae_of_all _ hM
  have hBf : ∀ᵐ b ∂μT, ‖f b‖ ≤ B + M := by
    filter_upwards [hBv, hvf] with b hb hf
    rw [← hf]
    exact (norm_add_le _ _).trans (add_le_add hb (hM b))
  obtain ⟨MB, CB, _hEc, hEM, hElog, _hEdiv⟩ :=
    S.exists_physicalLabelCommonField_bounds hq hqper hM
  let E := S.physicalLabelCommonField q
  let V : ℝ := B + (∫ b, ‖w b‖) + MB
  let U : ℝ := (B + M) * ∫ z in torusBox, ‖torusBiotSavartKernel z‖
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) :
      ‖vy t a‖ ≤ V := by
    rw [heqY t ht a ha]
    have hi := norm_planarMaterialBiotSavart_le_sum hw hB
      (YH ⟨t, ht⟩) (hY ⟨t, ht⟩) (Y t a)
    rw [hYH] at hi
    exact (norm_add_le _ _).trans (add_le_add hi (hEM t _))
  have hqdisp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) :
      ‖Y t a - a‖ ≤ V * t := by
    have hh := norm_trajectory_sub_time_le (v := fun s _ => vy s a)
      (fun s hs => hYd s hs a ha) (fun s hs _ => hv s hs a ha)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT⟩) ht
    simpa only [hinit a ha, sub_zero, abs_of_nonneg ht.1] using hh
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) :
      ‖S.forward t a - Y t a‖ ≤ (U + V) * T := by
    calc
      _ ≤ ‖S.forward t a - a‖ + ‖a - Y t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ U * t + V * t := add_le_add (S.displacement_le hT hBf ht a)
        (by rw [norm_sub_rev]; exact hqdisp t ht a ha)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 (add_nonneg hU hV)]
  let vx : ℝ → R2 → R2 := fun t a =>
    particleVelocityRepresentative f S.backward S.backward_area t (S.forward t a)
  have hVc : Continuous (Function.uncurry
      (particleVelocityRepresentative f S.backward S.backward_area)) :=
    continuous_particleVelocityRepresentative f (add_nonneg hB0 hM0)
      hBf S.backward_area S.backward_continuous
  have hvc (a : R2) : Continuous (fun t => vx t a) := by
    let j : ℝ → ℝ × R2 := fun t => (t, S.forward t a)
    have hj : Continuous j := continuous_id.prodMk
      (S.forward_continuous.comp (continuous_id.prodMk continuous_const))
    exact hVc.comp (f := j) hj
  apply hybrid_local_material_particle_uniqueness_active_log_common
    hw hB hwzero (show 0 ≤ (U + V) * T by positivity) MB.2 CB.2 hactive
    S.forward Y vx vy E S.forward_area YH hYH hY
    (fun t _ => hEM t) (fun t _ => hElog t) hsmall (fun a _ => hvc a) hyc
    (fun t ht a _ => S.derivative t ht a) hYd
    (fun a ha => (S.initial a).trans (hinit a ha).symm) hbound ?_ heqY
  intro t ht a ha
  have he := S.particleVelocityRepresentative_eq_partialMaterial_add_commonField
    hvint hqint hvper hqper hvf hBv hBq ht (S.forward t a) (hinnerSmall t ht a ha)
  change vx t a = _
  rw [show vx t a = periodicLocalMaterialVelocity v (S.forward t) (S.forward t a) +
    S.physicalLabelCommonField q t (S.forward t a) from he]
  congr 1
  unfold periodicLocalMaterialVelocity
  apply integral_congr_ae
  filter_upwards [hwv] with b hb
  rw [hb]

end BoundedEulerParticleSystem
end Euler2D

end
