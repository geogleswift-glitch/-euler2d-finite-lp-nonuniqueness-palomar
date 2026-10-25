module

public import RequestProject.Euler.CircularReferencePhases

/-! The actual full-period derivative is exactly the identity on
independent tangential mean perturbations. The proof differentiates a
genuine family of periodic reference contours in the original Banach norm. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) neutralMeanLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) neutralMeanLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularReferencePhaseCurve {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (τ : Fin 2 → ℝ) (s : ℝ) (i : Fin 2) : LittleContourSpace γ :=
  Real.cos (τ i * s) • littleCircularReference hγ hγ1 i +
    Real.sin (τ i * s) • contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)

def circularTangentialMeanLittle {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (τ : Fin 2 → ℝ) (i : Fin 2) : LittleContourSpace γ :=
  τ i • contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)

theorem circularReferencePhaseCurve_eq_parameterShift {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (τ : Fin 2 → ℝ) (s : ℝ) :
    circularReferencePhaseCurve hγ hγ1 τ s =
      contourParameterShiftFamilyCLM γ (fun i => τ i * s) (littleCircularReference hγ hγ1) := by
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective x
  change (Real.cos (τ i * s) : ℝ) • refCircle (circularContourRadii i) θ +
    (Real.sin (τ i * s) : ℝ) • LittleContourSpace.lift γ
      (contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)) θ =
        LittleContourSpace.lift γ
          (contourParameterShiftLittleCLM γ (τ i * s) (littleCircularReference hγ hγ1 i)) θ
  rw [lift_contourParameterShiftLittleCLM, lift_contourParameterShiftLittleCLM]
  exact (refCircle_phase_decomposition (circularContourRadii i) θ (τ i * s)).symm

theorem circularReferencePhaseCurve_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (τ : Fin 2 → ℝ) :
    circularReferencePhaseCurve hγ hγ1 τ 0 = littleCircularReference hγ hγ1 := by
  funext i
  simp only [circularReferencePhaseCurve, mul_zero, Real.cos_zero, Real.sin_zero,
    one_smul, _root_.zero_smul, add_zero]

theorem hasDerivAt_circularReferencePhaseCurve_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (τ : Fin 2 → ℝ) :
    HasDerivAt (circularReferencePhaseCurve hγ hγ1 τ) (circularTangentialMeanLittle hγ hγ1 τ) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have hp := (hasDerivAt_id (0 : ℝ)).const_mul (τ i)
  simpa only [circularReferencePhaseCurve, circularTangentialMeanLittle, Pi.add_def, Function.comp_def,
    id_eq, mul_one, mul_zero, Real.cos_zero, Real.sin_zero, neg_zero, zero_mul, one_mul,
    _root_.zero_smul, zero_add] using
    (((Real.hasDerivAt_cos _).comp 0 hp).smul_const (littleCircularReference hγ hγ1 i)).add
      (((Real.hasDerivAt_sin _).comp 0 hp).smul_const
        (contourParameterShiftLittleCLM γ (Real.pi / 2) (littleCircularReference hγ hγ1 i)))

theorem circularPeriod_derivative_tangentialMean {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) ρ) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (τ : Fin 2 → ℝ) :
    fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)
        (circularTangentialMeanLittle hγ hγ1 τ) = circularTangentialMeanLittle hγ hγ1 τ := by
  let α := circularReferencePhaseCurve hγ hγ1 τ
  have hα := hasDerivAt_circularReferencePhaseCurve_zero hγ hγ1 τ
  have hball : ∀ᶠ s : ℝ in 𝓝 0, α s ∈ ball (littleCircularReference hγ hγ1) ρ :=
    hα.continuousAt (by rw [circularReferencePhaseCurve_zero]; exact ball_mem_nhds _ hρ)
  have he : (fun s => X (α s) period) =ᶠ[𝓝 0] α := by
    filter_upwards [hball] with s hs
    dsimp only [α] at hs ⊢
    rw [circularReferencePhaseCurve_eq_parameterShift] at hs ⊢
    exact circularPeriod_fixes_parameterShift_reference hγ hγ1 hX _ hs
  have hP : HasFDerivAt (fun W => X W period)
      (fderiv ℝ (fun W => X W period) (littleCircularReference hγ hγ1)) (α 0) := by
    change HasFDerivAt _ _ (circularReferencePhaseCurve hγ hγ1 τ 0)
    rw [circularReferencePhaseCurve_zero]
    exact hd.hasFDerivAt
  exact (hP.comp_hasDerivAt 0 hα).unique (hα.congr_of_eventuallyEq he)

end Euler2D

end
