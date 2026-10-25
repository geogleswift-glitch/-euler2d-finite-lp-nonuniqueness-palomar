module

public import RequestProject.Euler.TorusPhysicalSourceContinuity
public import RequestProject.Euler.ActualTorusContourField

/-! A real time-dependent Little contour forcing for the actual Euler
source. Time clipping uses only the proved physical support window. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_clamped_actualTorusCorrection_LittleField
    (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    (hmean : (∫ x in torusBox, f x) = 0)
    {ε a : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) (ha : 0 < a) (ha16 : a ≤ 1 / 16)
    (hsupp : ∀ t ∈ Icc (0 : ℝ) ε, ∀ x ∈ torusBox,
      a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0)
    {γ : ℝ≥0} (hγ1 : (γ : ℝ) ≤ 1) :
    ∃ K : ℝ≥0, ∃ E : ℝ → LittleContourSpace γ → LittleContourSpace γ,
      (∀ t Z, ‖Z‖ < a / 4 → ∀ θ,
        LittleContourSpace.lift γ (E t Z) θ =
          actualTorusCorrectionVelocity
            (S.physicalComplexSource w (projIcc 0 ε hε.le t))
            (LittleContourSpace.lift γ Z θ)) ∧
      (∀ t, LipschitzOnWith K (E t) (ball 0 (a / 4))) ∧
      (∀ Z ∈ ball (0 : LittleContourSpace γ) (a / 4), Continuous (fun t => E t Z)) ∧
      (∀ t ∈ Icc (0 : ℝ) ε, ∀ Z, ‖Z‖ < a / 4 → ∀ θ,
        LittleContourSpace.lift γ (E t Z) θ =
          actualTorusCorrectionVelocity (S.physicalComplexSource w t)
            (LittleContourSpace.lift γ Z θ)) := by
  let τ : ℝ → ℝ := fun t => projIcc 0 ε hε.le t
  have hτ : Continuous τ := continuous_subtype_val.comp continuous_projIcc
  have hτmem (t : ℝ) : τ t ∈ Icc (0 : ℝ) ε := (projIcc 0 ε hε.le t).property
  have hτT (t : ℝ) : τ t ∈ Icc (0 : ℝ) T := ⟨(hτmem t).1, (hτmem t).2.trans hεT⟩
  let v : ℝ → ℂ → ℝ := fun t => S.physicalComplexSource w (τ t)
  have hv (t : ℝ) : Integrable (v t) := S.integrable_physicalComplexSource hwf _
  have hvs (t : ℝ) : ∀ z, a < ‖z‖ → v t z = 0 :=
    S.physicalComplexSource_support (hsupp _ (hτmem t))
  have hvm (t : ℝ) : (∫ z, v t z) = 0 :=
    (S.integral_physicalComplexSource hwf _).trans hmean
  have hvy (t : ℝ) : ∀ z, v t (I * z) = v t z :=
    S.physicalComplexSource_fourfold hS hwper hwrot (by linarith) (hτT t)
      (hsupp _ (hτmem t))
  let M := a ^ 4 * (scalarL2L1Constant * ‖f‖)
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact mul_nonneg (by positivity)
      (mul_nonneg scalarL2L1Constant_nonneg (norm_nonneg _))
  have hvM (t : ℝ) : (∫ z : ℂ, ‖z‖ ^ 4 * |v t z|) ≤ M :=
    S.physicalComplexSource_fourthAbsoluteMoment_le hwf (hsupp _ (hτmem t))
  obtain ⟨K, hfield⟩ := exists_actualTorusCorrection_LittleField ha ha16 hM hγ1
  choose E hE hLip using fun t => hfield (v t) (hv t) (hvs t) (hvm t) (hvy t) (hvM t)
  refine ⟨K, E, hE, hLip, ?_, ?_⟩
  · intro Z hZ
    have hZn : ‖Z‖ < a / 4 := mem_ball_zero_iff.mp hZ
    apply continuous_iff_continuousAt.mpr
    intro s
    apply tendsto_actualTorusCorrection_of_L1 ha ha16 hγ1 hv (hv s) hvs (hvs s)
      hvm (hvm s) hvy (hvy s) (show 0 < a / 4 by positivity)
      (show (0 : ℝ) ≤ 1 by norm_num) (show ((1 : ℝ) + 1) * (a / 4) ≤ a / 2 by linarith)
      Z (by simpa only [one_mul] using hZn.le) (fun t => hE t Z hZn) (hE s Z hZn)
    exact S.tendsto_physicalComplexSource_L1 hwf (hτ.tendsto s)
  · intro t ht Z hZ θ
    have hh := hE t Z hZ θ
    simpa only [v, τ, projIcc_of_mem hε.le ht] using hh

end BoundedEulerParticleSystem

end Euler2D

end
