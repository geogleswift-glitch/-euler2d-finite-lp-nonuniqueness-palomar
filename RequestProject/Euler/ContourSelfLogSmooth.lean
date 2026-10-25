module

public import RequestProject.Euler.ContourSelfLogBaseSmooth
public import RequestProject.Euler.ContourLogDerivativeAnalytic
public import RequestProject.Euler.ContourBaseDerivativeCoordinates
public import RequestProject.Euler.BoundedBelowCalculus
public import RequestProject.Euler.ContourLittleSelfLog

/-! The literal self-log contour operator has every finite order of
Banach-input smoothness in the actual little Hölder target.  The base
value and genuine spatial derivative are lifted through the proved
bounded-below coordinates and the actual closed little subspace. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) selfLogSmoothC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) selfLogSmoothC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) selfLogSmoothLittle_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) selfLogSmoothLittle_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) :=
  Submodule.normedSpace (LittleContourSpace γ)

variable {γ : ℝ≥0}

def nearCircleSelfLogLittleTotal (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (Z : LittleContourSpace γ) :
    LittleContourSpace γ :=
  if h : ‖Z.val - Z₀‖ < 2 * r / Real.pi then
    nearCircleSelfLogLittle hγ hγ1 Z₀ hr href ⟨Z, h⟩ else 0

@[simp] theorem nearCircleSelfLogLittleTotal_of_mem (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1)
    (Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (Z : LittleContourSpace γ)
    (hZ : ‖Z.val - Z₀‖ < 2 * r / Real.pi) :
    nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href Z =
      nearCircleSelfLogLittle hγ hγ1 Z₀ hr href ⟨Z, hZ⟩ := dif_pos hZ

theorem contourBaseDerivativeMap_nearCircleSelfLogLittleTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : LittleContourSpace γ) (hZ : ‖Z.val - Z₀‖ < 2 * r / Real.pi) :
    contourBaseDerivativeMap γ (nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href Z).val =
      (ContourC1Space.selfLogIntegral Z.val 0, analyticContourLogDerivativeHolder hγ hγ1 Z.val) := by
  rw [nearCircleSelfLogLittleTotal_of_mem hγ hγ1 Z₀ hr href Z hZ,
    contourBaseDerivativeMap_apply]
  apply Prod.ext
  · rfl
  · exact (analyticContourLogDerivativeHolder_eq_positive hγ hγ1
      (nearCirclePositiveContour Z₀ hr href ⟨Z, hZ⟩)).symm

theorem contDiffOn_nearCircleSelfLogC1Total
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) (n : ℕ∞) :
    ContDiffOn ℝ n (fun Z : LittleContourSpace γ =>
      (nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href Z).val)
      {Z | ‖Z.val - Z₀‖ < 2 * r / Real.pi} := by
  let U : Set (LittleContourSpace γ) := {Z | ‖Z.val - Z₀‖ < 2 * r / Real.pi}
  have hU : IsOpen U :=
    isOpen_lt (((LittleContourSpace.inclusion γ).continuous.sub continuous_const).norm) continuous_const
  have himage : MapsTo (LittleContourSpace.inclusion γ) U
      {Z : ContourC1Space γ | ContourC1Space.HasPositiveChordArc Z} := by
    intro Z hZ
    exact (nearCirclePositiveContour Z₀ hr href ⟨Z, hZ⟩).property
  have hbase : ContDiffOn ℝ n (fun Z : LittleContourSpace γ =>
      ContourC1Space.selfLogIntegral Z.val 0) U :=
    ((contDiffOn_selfLogIntegral_fixed hγ 0).of_le
      (WithTop.coe_le_coe.mpr le_top)).comp
        (LittleContourSpace.inclusion γ).contDiff.contDiffOn himage
  have hderiv : ContDiffOn ℝ n (fun Z : LittleContourSpace γ =>
      analyticContourLogDerivativeHolder hγ hγ1 Z.val) U :=
    (contDiffOn_contourLogDerivativeHolder hγ hγ1 (n : WithTop ℕ∞)).comp
      (LittleContourSpace.inclusion γ).contDiff.contDiffOn himage
  apply (contDiffOn_boundedBelowLinearMap_iff (contourBaseDerivativeMap γ)
    (show 0 < Real.pi + 2 by positivity) norm_contourC1_le_baseDerivativeMap n hU _).mp
  exact (hbase.prodMk hderiv).congr (fun Z hZ =>
    contourBaseDerivativeMap_nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href Z hZ)

/-- Every finite order, including order three and genuine infinite
smoothness, holds in the unchanged actual little Hölder norm. -/
theorem contDiffOn_nearCircleSelfLogLittleTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) (n : ℕ∞) :
    ContDiffOn ℝ n (nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href)
      {Z : LittleContourSpace γ | ‖Z.val - Z₀‖ < 2 * r / Real.pi} := by
  have hU : IsOpen {Z : LittleContourSpace γ | ‖Z.val - Z₀‖ < 2 * r / Real.pi} :=
    isOpen_lt (((LittleContourSpace.inclusion γ).continuous.sub continuous_const).norm) continuous_const
  exact (contDiffOn_closedSubmodule_iff (LittleContourSpace γ) (isClosed_littleContourSpace γ)
    n hU (nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href)).mp
      (contDiffOn_nearCircleSelfLogC1Total hγ hγ1 Z₀ hr href n)

theorem contDiffAt_nearCircleSelfLogLittleTotal
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : LittleContourSpace γ) (hZ : ‖Z.val - Z₀‖ < 2 * r / Real.pi) (n : ℕ∞) :
    ContDiffAt ℝ n (nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href) Z := by
  have hU : IsOpen {W : LittleContourSpace γ | ‖W.val - Z₀‖ < 2 * r / Real.pi} :=
    isOpen_lt (((LittleContourSpace.inclusion γ).continuous.sub continuous_const).norm) continuous_const
  exact (contDiffOn_nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href n Z hZ).contDiffAt
    (hU.mem_nhds hZ)

@[simp] theorem lift_nearCircleSelfLogLittleTotal_of_mem
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : LittleContourSpace γ) (hZ : ‖Z.val - Z₀‖ < 2 * r / Real.pi) :
    LittleContourSpace.lift γ (nearCircleSelfLogLittleTotal hγ hγ1 Z₀ hr href Z) =
      ContourC1Space.selfLogIntegral Z.val := by
  rw [nearCircleSelfLogLittleTotal_of_mem hγ hγ1 Z₀ hr href Z hZ]
  rfl

end Euler2D

end
