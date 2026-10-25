module

public import RequestProject.Euler.ContourAreaAnalytic

/-!
# The actual analytic fixed-area chart on the little contour Banach space

The coefficient and the resulting loop agree exactly with the original
`chartCoeff` and `areaChart`.  The analytic map and its derivative are proved
from the actual quadratic area form and the actual smooth reference circle.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal BoundedContinuousFunction ContDiff

namespace Euler2D

namespace LittleContourSpace

@[simp] theorem lift_zero (γ : ℝ≥0) : lift γ (0 : LittleContourSpace γ) = 0 := rfl
@[simp] theorem lift_add {γ : ℝ≥0} (f g : LittleContourSpace γ) :
    lift γ (f + g) = lift γ f + lift γ g := rfl
@[simp] theorem lift_smul {γ : ℝ≥0} (c : ℝ) (f : LittleContourSpace γ) :
    lift γ (c • f) = c • lift γ f := rfl

end LittleContourSpace

@[simp] theorem littleContourArea_zero (γ : ℝ≥0) : littleContourArea γ 0 = 0 :=
  contourArea_zero γ

/-- The genuine closed linear area constraint in the actual little space. -/
abbrev LittleContourAreaConstraint (γ : ℝ≥0) (r : ℝ) := (littleContourEllCLM γ r).ker

theorem isClosed_littleContourAreaConstraint (γ : ℝ≥0) (r : ℝ) :
    IsClosed (LittleContourAreaConstraint γ r : Set (LittleContourSpace γ)) :=
  isClosed_eq (littleContourEllCLM γ r).continuous continuous_const

instance littleContourAreaConstraint_complete (γ : ℝ≥0) (r : ℝ) :
    CompleteSpace (LittleContourAreaConstraint γ r) :=
  (isClosed_littleContourAreaConstraint γ r).completeSpace_coe

/-- The actual original area-correction coefficient on the little space. -/
def littleChartCoeff (γ : ℝ≥0) (r : ℝ) (v : LittleContourSpace γ) : ℝ :=
  chartCoeff r (LittleContourSpace.lift γ v)

@[simp] theorem littleChartCoeff_zero (γ : ℝ≥0) (r : ℝ) : littleChartCoeff γ r 0 = 0 := by
  change Real.sqrt (1 - littleContourArea γ 0 / (Real.pi * r ^ 2)) - 1 = 0
  simp

theorem analyticAt_littleChartCoeff {γ : ℝ≥0} (r : ℝ) (v : LittleContourSpace γ)
    (hpos : 0 < 1 - littleContourArea γ v / (Real.pi * r ^ 2)) :
    AnalyticAt ℝ (littleChartCoeff γ r) v := by
  have hi : AnalyticAt ℝ (fun w : LittleContourSpace γ =>
      1 - littleContourArea γ w / (Real.pi * r ^ 2)) v :=
    analyticAt_const.sub (analyticAt_littleContourArea v).div_const
  exact ((analyticAt_real_sqrt_pos hpos).comp
    (f := fun w : LittleContourSpace γ => 1 - littleContourArea γ w / (Real.pi * r ^ 2)) hi).sub
      analyticAt_const

private theorem hasFDerivAt_sqrt_correction_zero {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (A : V → ℝ)
    (hA₀ : A 0 = 0) (hA : HasFDerivAt A (0 : V →L[ℝ] ℝ) 0) (D : ℝ) :
    HasFDerivAt (fun v => Real.sqrt (1 - A v / D) - 1) (0 : V →L[ℝ] ℝ) 0 := by
  have hd : HasFDerivAt (fun v : V => A v / D) (0 : V →L[ℝ] ℝ) 0 := by
    simpa only [Pi.smul_def, smul_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hA.const_smul D⁻¹
  have hi : HasFDerivAt (fun v : V => 1 - A v / D) (0 : V →L[ℝ] ℝ) 0 := by
    simpa only [Pi.sub_def, sub_zero] using (hasFDerivAt_const (1 : ℝ) (0 : V)).sub hd
  have hs := hi.sqrt (by simp [hA₀] : (1 - A 0 / D) ≠ 0)
  simpa only [smul_zero] using hs.sub_const 1

theorem hasFDerivAt_littleChartCoeff_zero (γ : ℝ≥0) (r : ℝ) :
    HasFDerivAt (littleChartCoeff γ r) (0 : LittleContourSpace γ →L[ℝ] ℝ) 0 :=
  hasFDerivAt_sqrt_correction_zero (littleContourArea γ) (littleContourArea_zero γ)
    (hasFDerivAt_littleContourArea_zero γ) (Real.pi * r ^ 2)

/-- The paper's actual area chart as a map between actual Banach spaces. -/
def littleAreaChart {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ)
    (v : LittleContourSpace γ) : LittleContourSpace γ :=
  (1 + littleChartCoeff γ r v) • littleReferenceCircle hγ₀ hγ₁ r + v

theorem lift_littleAreaChart {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ)
    (v : LittleContourSpace γ) :
    LittleContourSpace.lift γ (littleAreaChart hγ₀ hγ₁ r v) =
      areaChart r (LittleContourSpace.lift γ v) := by
  simp only [littleAreaChart, LittleContourSpace.lift_add, LittleContourSpace.lift_smul,
    lift_littleReferenceCircle]
  funext θ
  exact congrArg (fun z : ℂ => z + LittleContourSpace.lift γ v θ)
    Complex.real_smul

@[simp] theorem littleAreaChart_zero {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ) :
    littleAreaChart hγ₀ hγ₁ r 0 = littleReferenceCircle hγ₀ hγ₁ r := by
  simp [littleAreaChart]

private theorem analyticAt_scalar_correction {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (c : V → ℝ) (v : V)
    (hc : AnalyticAt ℝ c v) (z₀ : V) :
    AnalyticAt ℝ (fun w => (1 + c w) • z₀ + w) v :=
  ((analyticAt_const.add hc).smul analyticAt_const).add analyticAt_id

theorem analyticAt_littleAreaChart {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    (r : ℝ) (v : LittleContourSpace γ)
    (hpos : 0 < 1 - littleContourArea γ v / (Real.pi * r ^ 2)) :
    AnalyticAt ℝ (littleAreaChart hγ₀ hγ₁ r) v :=
  analyticAt_scalar_correction (littleChartCoeff γ r) v (analyticAt_littleChartCoeff r v hpos)
    (littleReferenceCircle hγ₀ hγ₁ r)

private theorem hasFDerivAt_scalar_correction_identity {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (c : V → ℝ)
    (hc₀ : HasFDerivAt c (0 : V →L[ℝ] ℝ) 0) (z₀ : V) :
    HasFDerivAt (fun v => (1 + c v) • z₀ + v) (ContinuousLinearMap.id ℝ V) 0 := by
  have hc : HasFDerivAt (fun v : V => 1 + c v) (0 : V →L[ℝ] ℝ) 0 := by
    simpa only [Pi.add_def, add_zero] using
      (hasFDerivAt_const (1 : ℝ) (0 : V)).add hc₀
  have hd := (hc.smul_const z₀).add (hasFDerivAt_id (0 : V))
  simpa only [Pi.add_def, id_eq, ContinuousLinearMap.zero_smulRight, zero_add] using hd

theorem hasFDerivAt_littleAreaChart_zero {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ) :
    HasFDerivAt (littleAreaChart hγ₀ hγ₁ r)
      (ContinuousLinearMap.id ℝ (LittleContourSpace γ)) 0 :=
  hasFDerivAt_scalar_correction_identity (littleChartCoeff γ r)
    (hasFDerivAt_littleChartCoeff_zero γ r) (littleReferenceCircle hγ₀ hγ₁ r)

/-- A genuine norm neighborhood of zero on which the original chart is analytic. -/
theorem exists_littleAreaChart_analytic_radius {γ : ℝ≥0}
    (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1) (r : ℝ) :
    ∃ ε > 0, ∀ v : LittleContourSpace γ, ‖v‖ < ε →
      0 < 1 - littleContourArea γ v / (Real.pi * r ^ 2) ∧
        AnalyticAt ℝ (littleAreaChart hγ₀ hγ₁ r) v := by
  have hc : Continuous (fun v : LittleContourSpace γ =>
      1 - littleContourArea γ v / (Real.pi * r ^ 2)) :=
    continuous_const.sub
      (((continuous_contourArea γ).comp (LittleContourSpace.inclusion γ).continuous).div_const _)
  have hp : ∀ᶠ v in 𝓝 (0 : LittleContourSpace γ),
      0 < 1 - littleContourArea γ v / (Real.pi * r ^ 2) :=
    hc.continuousAt.eventually (eventually_gt_nhds (by simp))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hp
  refine ⟨ε, hε, fun v hv => ?_⟩
  have hpos := hball (y := v) (by
    rw [Subtype.dist_eq, Submodule.coe_zero, dist_zero_right]
    exact (Submodule.norm_coe v).trans_lt hv)
  exact ⟨hpos, analyticAt_littleAreaChart hγ₀ hγ₁ r v hpos⟩

theorem loopArea_littleAreaChart {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    {r : ℝ} (hr : r ≠ 0) (v : LittleContourSpace γ)
    (hℓ : littleContourEllCLM γ r v = 0)
    (hA : littleContourArea γ v ≤ Real.pi * r ^ 2) :
    loopArea (LittleContourSpace.lift γ (littleAreaChart hγ₀ hγ₁ r v)) = Real.pi * r ^ 2 := by
  rw [lift_littleAreaChart]
  apply loopArea_areaChart hr (LittleContourSpace.contDiff_lift v)
    (LittleContourSpace.periodic_lift v)
  · rwa [← littleContourEllCLM_eq_ellFun]
  · exact hA

/-- On a genuine norm neighborhood, the analytic chart sends the actual
closed linear area constraint to loops of exactly the prescribed area. -/
theorem exists_littleFixedAreaChart_radius {γ : ℝ≥0} (hγ₀ : 0 < γ) (hγ₁ : γ ≤ 1)
    {r : ℝ} (hr : r ≠ 0) :
    ∃ ε > 0, ∀ v : LittleContourSpace γ, ‖v‖ < ε → littleContourEllCLM γ r v = 0 →
      AnalyticAt ℝ (littleAreaChart hγ₀ hγ₁ r) v ∧
        loopArea (LittleContourSpace.lift γ (littleAreaChart hγ₀ hγ₁ r v)) = Real.pi * r ^ 2 := by
  obtain ⟨ε, hε, hball⟩ := exists_littleAreaChart_analytic_radius hγ₀ hγ₁ r
  refine ⟨ε, hε, fun v hv hℓ => ?_⟩
  obtain ⟨hpos, ha⟩ := hball v hv
  have hden : 0 < Real.pi * r ^ 2 := by positivity
  have hquot : littleContourArea γ v / (Real.pi * r ^ 2) < 1 := by linarith
  have hA : littleContourArea γ v ≤ Real.pi * r ^ 2 := ((div_lt_one hden).mp hquot).le
  exact ⟨ha, loopArea_littleAreaChart hγ₀ hγ₁ hr v hℓ hA⟩

/-- The existing coefficient-uniqueness theorem applies to every actual
little-space loop with the genuine closed linear constraint. -/
theorem littleChartCoeff_unique {γ : ℝ≥0} {r : ℝ} (hr : r ≠ 0)
    (v : LittleContourSpace γ) (hℓ : littleContourEllCLM γ r v = 0)
    {t : ℝ} (ht : 0 < 1 + t)
    (hA : loopArea (fun θ => ((1 + t : ℝ) : ℂ) * refCircle r θ +
      LittleContourSpace.lift γ v θ) = Real.pi * r ^ 2) :
    t = littleChartCoeff γ r v := by
  apply chart_coeff_unique hr (LittleContourSpace.contDiff_lift v)
    (LittleContourSpace.periodic_lift v) _ ht hA
  rwa [← littleContourEllCLM_eq_ellFun]

end Euler2D

end
