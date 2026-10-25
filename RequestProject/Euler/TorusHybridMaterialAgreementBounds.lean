module
public import RequestProject.Euler.TorusHybridMaterialAgreement

/-! The mixed material identification needs no assumed uniform distance
bound: genuine velocity bounds yield one on every finite time window. -/
@[expose] public section
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology Metric Real
open scoped NNReal ENNReal
namespace Euler2D
namespace BoundedEulerParticleSystem
variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_uniform_bound_correctionLabelField :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t x, ‖S.correctionLabelField t x‖ ≤ M := by
  obtain ⟨C, hC, _, _⟩ := exists_torusGreenCorrection_perpGradient_bounds
  have hw : Integrable (fun b => ‖f b‖) μT := ((Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)).norm
  refine ⟨(C : ℝ) * ∫ b in torusBox, ‖f b‖, by positivity, fun t x => ?_⟩
  unfold correctionLabelField
  calc
    _ ≤ ∫ b in torusBox, (C : ℝ) * ‖f b‖ := by
      apply norm_integral_le_of_norm_le (hw.const_mul _)
      exact ae_of_all _ fun b => by
        rw [norm_smul, mul_comm (C : ℝ)]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem forward_eq_plane_material_active_of_velocity_bounds
    {w v : R2 → ℝ} {B : ℝ} {A : Set R2}
    (hw : Integrable w) (hB : ∀ b, ‖w b‖ ≤ B)
    (hwzero : ∀ b, b ∉ torusBox → w b = 0)
    (hwv : w =ᵐ[μT] v) (hvf : v =ᵐ[μT] (f : R2 → ℝ)) (hvper : IsTorusPeriodic v)
    (hT : 0 ≤ T) (hactive : ∀ᵐ b ∂μT, w b ≠ 0 → b ∈ A)
    (Y vy : ℝ → R2 → R2)
    (YH : Icc (0 : ℝ) T → R2 ≃ₜ R2)
    (hYH : ∀ t, (YH t : R2 → R2) = Y t)
    (hY : ∀ t, MeasurePreserving (YH t) volume volume)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      ∀ᵐ b ∂μT, w b ≠ 0 → ‖S.forward t a - S.forward t b‖ ≤ 1 / 2)
    (hyc : ∀ a ∈ A, Continuous (fun t => vy t a))
    (hYd : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, HasDerivAt (fun s => Y s a) (vy t a) t)
    (hinit : ∀ a ∈ A, Y 0 a = a)
    (heqY : ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A,
      vy t a = planarMaterialLabelVelocity kernelK w (Y t) (Y t a) + S.correctionLabelField t (Y t a)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ A, S.forward t a = Y t a := by
  obtain ⟨M, hM, hMb⟩ := S.exists_uniform_bound_correctionLabelField
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hBf : ∀ᵐ b ∂μT, ‖f b‖ ≤ B := by
    filter_upwards [hwv.trans hvf] with b hb
    rw [← hb]
    exact hB b
  let V : ℝ := B + (∫ b, ‖w b‖) + M
  let U : ℝ := B * ∫ z in torusBox, ‖torusBiotSavartKernel z‖
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) : ‖vy t a‖ ≤ V := by
    rw [heqY t ht a ha]
    have hi := norm_planarMaterialBiotSavart_le_sum hw hB (YH ⟨t, ht⟩) (hY ⟨t, ht⟩) (Y t a)
    rw [hYH] at hi
    exact (norm_add_le _ _).trans (add_le_add hi (hMb t _))
  have hq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) : ‖Y t a - a‖ ≤ V * t := by
    have hh := norm_trajectory_sub_time_le (v := fun s _ => vy s a)
      (fun s hs => hYd s hs a ha) (fun s hs _ => hv s hs a ha)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) T from ⟨le_rfl, hT⟩) ht
    simpa only [hinit a ha, sub_zero, abs_of_nonneg ht.1] using hh
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) (ha : a ∈ A) :
      ‖S.forward t a - Y t a‖ ≤ (U + V) * T := by
    calc
      _ ≤ ‖S.forward t a - a‖ + ‖a - Y t a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ U * t + V * t := add_le_add (S.displacement_le hT hBf ht a)
        (by rw [norm_sub_rev]; exact hq t ht a ha)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ht.2 (add_nonneg hU hV)]
  exact S.forward_eq_plane_material_active hw hB hwzero hwv hvf hvper (by positivity)
    hactive Y vy YH hYH hY hsmall hyc hYd hinit hb heqY

end BoundedEulerParticleSystem
end Euler2D
end
