module

public import RequestProject.Euler.CircularFourierConstraints

/-! A bounded projection onto the original linear area constraint, and
the genuine inverse of the actual analytic area chart near the circle. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) areaInverseLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) areaInverseLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def littleAreaRadialCoeffCLM (γ : ℝ≥0) (r : ℝ) : LittleContourSpace γ →L[ℝ] ℝ :=
  (2 * Real.pi * r ^ 2)⁻¹ • littleContourEllCLM γ r

theorem littleAreaRadialCoeffCLM_apply {γ : ℝ≥0} (r : ℝ) (v : LittleContourSpace γ) :
    littleAreaRadialCoeffCLM γ r v = littleContourEllCLM γ r v / (2 * Real.pi * r ^ 2) := by
  change (2 * Real.pi * r ^ 2)⁻¹ * littleContourEllCLM γ r v = _
  rw [div_eq_mul_inv, mul_comm]

def littleAreaTangentProjection {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    LittleContourSpace γ →L[ℝ] LittleContourSpace γ :=
  ContinuousLinearMap.id ℝ (LittleContourSpace γ) -
    (littleAreaRadialCoeffCLM γ r).smulRight (littleReferenceCircle hγ hγ1 r)

theorem littleAreaTangentProjection_apply {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (r : ℝ) (v : LittleContourSpace γ) :
    littleAreaTangentProjection hγ hγ1 r v =
      v - (littleContourEllCLM γ r v / (2 * Real.pi * r ^ 2)) • littleReferenceCircle hγ hγ1 r := by
  change v - (littleAreaRadialCoeffCLM γ r v) • littleReferenceCircle hγ hγ1 r = _
  rw [littleAreaRadialCoeffCLM_apply]

theorem littleContourEllCLM_referenceCircle {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    littleContourEllCLM γ r (littleReferenceCircle hγ hγ1 r) = 2 * Real.pi * r ^ 2 := by
  rw [littleContourEllCLM_eq_ellFun, lift_littleReferenceCircle]
  exact ellFun_refCircle r

theorem littleAreaTangentProjection_ell_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : r ≠ 0) (v : LittleContourSpace γ) :
    littleContourEllCLM γ r (littleAreaTangentProjection hγ hγ1 r v) = 0 := by
  rw [littleAreaTangentProjection_apply, map_sub, map_smul, littleContourEllCLM_referenceCircle,
    smul_eq_mul, div_mul_cancel₀ _ (by positivity : 2 * Real.pi * r ^ 2 ≠ 0), sub_self]

theorem littleAreaTangentProjection_of_ell_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) (v : LittleContourSpace γ)
    (hv : littleContourEllCLM γ r v = 0) :
    littleAreaTangentProjection hγ hγ1 r v = v := by
  rw [littleAreaTangentProjection_apply, hv, zero_div, zero_smul, sub_zero]

theorem littleAreaTangentProjection_referenceCircle {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : r ≠ 0) :
    littleAreaTangentProjection hγ hγ1 r (littleReferenceCircle hγ hγ1 r) = 0 := by
  rw [littleAreaTangentProjection_apply, littleContourEllCLM_referenceCircle,
    div_self (by positivity : 2 * Real.pi * r ^ 2 ≠ 0), one_smul, sub_self]

theorem littleAreaTangentProjection_fourfold {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) (v : LittleContourSpace γ)
    (hv : v ∈ fourfoldLittleContourSubmodule γ) :
    littleAreaTangentProjection hγ hγ1 r v ∈ fourfoldLittleContourSubmodule γ := by
  rw [littleAreaTangentProjection_apply]
  exact (fourfoldLittleContourSubmodule γ).sub_mem hv
    ((fourfoldLittleContourSubmodule γ).smul_mem _ (littleReferenceCircle_mem_fourfold hγ hγ1 r))

def littleAreaChartInverse {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ)
    (Z : LittleContourSpace γ) : LittleContourSpace γ :=
  littleAreaTangentProjection hγ hγ1 r (Z - littleReferenceCircle hγ hγ1 r)

theorem littleAreaChartInverse_ell_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : r ≠ 0) (Z : LittleContourSpace γ) :
    littleContourEllCLM γ r (littleAreaChartInverse hγ hγ1 r Z) = 0 :=
  littleAreaTangentProjection_ell_zero hγ hγ1 hr _

theorem littleAreaChartInverse_mem_fourfold_area {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : r ≠ 0) (Z : LittleContourSpace γ)
    (hZ : Z ∈ fourfoldLittleContourSubmodule γ) :
    littleAreaChartInverse hγ hγ1 r Z ∈
      fourfoldLittleContourSubmodule γ ⊓ LittleContourAreaConstraint γ r := by
  refine ⟨littleAreaTangentProjection_fourfold hγ hγ1 r _
    ((fourfoldLittleContourSubmodule γ).sub_mem hZ (littleReferenceCircle_mem_fourfold hγ hγ1 r)),
    littleAreaChartInverse_ell_zero hγ hγ1 hr Z⟩

theorem analyticAt_littleAreaChartInverse {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) (Z : LittleContourSpace γ) :
    AnalyticAt ℝ (littleAreaChartInverse hγ hγ1 r) Z := by
  have hi : AnalyticAt ℝ (fun W : LittleContourSpace γ => W - littleReferenceCircle hγ hγ1 r) Z :=
    analyticAt_id.sub analyticAt_const
  exact ((littleAreaTangentProjection hγ hγ1 r).analyticAt
    (Z - littleReferenceCircle hγ hγ1 r)).comp
      (f := fun W : LittleContourSpace γ => W - littleReferenceCircle hγ hγ1 r) hi

theorem littleAreaChartInverse_littleAreaChart {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : r ≠ 0) (v : LittleContourSpace γ)
    (hv : littleContourEllCLM γ r v = 0) :
    littleAreaChartInverse hγ hγ1 r (littleAreaChart hγ hγ1 r v) = v := by
  let P : LittleContourSpace γ →L[ℝ] LittleContourSpace γ := littleAreaTangentProjection hγ hγ1 r
  have hP : P (littleReferenceCircle hγ hγ1 r) = 0 :=
    littleAreaTangentProjection_referenceCircle hγ hγ1 hr
  change P (((1 + littleChartCoeff γ r v) • littleReferenceCircle hγ hγ1 r + v) -
    littleReferenceCircle hγ hγ1 r) = v
  have hscale : P ((1 + littleChartCoeff γ r v) • littleReferenceCircle hγ hγ1 r) =
      (1 + littleChartCoeff γ r v) • P (littleReferenceCircle hγ hγ1 r) :=
    P.toLinearMap.map_smul' _ _
  rw [P.map_sub, P.map_add, hscale, hP,
    smul_zero, sub_zero, zero_add]
  exact littleAreaTangentProjection_of_ell_zero hγ hγ1 r v hv

theorem littleAreaChartInverse_decomposition {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) (Z : LittleContourSpace γ) :
    Z = (1 + littleAreaRadialCoeffCLM γ r (Z - littleReferenceCircle hγ hγ1 r)) •
      littleReferenceCircle hγ hγ1 r + littleAreaChartInverse hγ hγ1 r Z := by
  rw [littleAreaChartInverse, littleAreaTangentProjection_apply,
    littleAreaRadialCoeffCLM_apply,
    add_smul (1 : ℝ) (littleContourEllCLM γ r (Z - littleReferenceCircle hγ hγ1 r) /
      (2 * Real.pi * r ^ 2)) (littleReferenceCircle hγ hγ1 r), one_smul]
  abel

theorem littleAreaChart_littleAreaChartInverse {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) {r : ℝ} (hr : r ≠ 0) (Z : LittleContourSpace γ)
    (hpos : 0 < 1 + littleAreaRadialCoeffCLM γ r (Z - littleReferenceCircle hγ hγ1 r))
    (harea : littleContourArea γ Z = Real.pi * r ^ 2) :
    littleAreaChart hγ hγ1 r (littleAreaChartInverse hγ hγ1 r Z) = Z := by
  have he := littleAreaChartInverse_decomposition hγ hγ1 r Z
  have hcoeff : littleAreaRadialCoeffCLM γ r (Z - littleReferenceCircle hγ hγ1 r) =
      littleChartCoeff γ r (littleAreaChartInverse hγ hγ1 r Z) := by
    apply littleChartCoeff_unique hr _ (littleAreaChartInverse_ell_zero hγ hγ1 hr Z) hpos
    have hlift := congrArg (LittleContourSpace.lift γ) he
    change loopArea _ = Real.pi * r ^ 2
    rw [← harea]
    congr 1
    funext θ
    have hv := congrFun hlift θ
    simp only [LittleContourSpace.lift_add, LittleContourSpace.lift_smul, Pi.add_apply,
      Pi.smul_apply, lift_littleReferenceCircle, Complex.real_smul] at hv
    exact hv.symm
  rw [littleAreaChart, ← hcoeff]
  exact he.symm

theorem exists_littleAreaChartInverse_positive_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (r : ℝ) :
    ∃ δ > 0, ∀ Z ∈ ball (littleReferenceCircle hγ hγ1 r) δ,
      0 < 1 + littleAreaRadialCoeffCLM γ r (Z - littleReferenceCircle hγ hγ1 r) := by
  have hc : Continuous (fun Z : LittleContourSpace γ =>
      1 + littleAreaRadialCoeffCLM γ r (Z - littleReferenceCircle hγ hγ1 r)) :=
    continuous_const.add ((littleAreaRadialCoeffCLM γ r).continuous.comp
      (continuous_id.sub continuous_const))
  have hp : ∀ᶠ Z in 𝓝 (littleReferenceCircle hγ hγ1 r),
      0 < 1 + littleAreaRadialCoeffCLM γ r (Z - littleReferenceCircle hγ hγ1 r) :=
    hc.continuousAt.eventually (eventually_gt_nhds (by simp))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hp
  exact ⟨δ, hδ, fun Z hZ => hball (by simpa only [mem_ball] using hZ)⟩

end Euler2D

end
