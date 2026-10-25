module

public import RequestProject.Euler.ContourLogDerivativeStrongContinuity
public import RequestProject.Euler.ContourSmoothSelfLogRange

/-! The original logarithmic self-interaction really preserves the little
Hölder space.  Smooth inputs have smooth outputs, and convergence takes
place in the actual C¹ Hölder norm before applying closedness. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

local instance (priority := 2000) littleSelfLogC1_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) :=
  Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

local instance (priority := 2000) littleSelfLogC1_normedSpace (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) :=
  Submodule.normedSpace (contourC1GraphSubmodule γ)

local instance (priority := 2000) littleSelfLog_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) :=
  Submodule.normedAddCommGroup (LittleContourSpace γ)

theorem nearCircleSelfLogC1_mem_little {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : NearCircleLittleContour Z₀ r) :
    nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z ∈
      (LittleContourSpace γ : Set (ContourC1Space γ)) := by
  classical
  let p := nearCirclePositiveContour Z₀ hr href Z
  obtain ⟨u, hs, hu, _, hlim⟩ := LittleContourSpace.exists_smooth_chord_approximation
    Z.val (positiveChordConstant_pos p) (hasChordArcLower_positiveChordConstant p)
  have hval : Tendsto (fun n => (u n).val) atTop (𝓝 Z.val.val) :=
    ((LittleContourSpace.inclusion γ).continuous.tendsto Z.val).comp hlim
  have hn : ∀ᶠ n in atTop, ‖(u n).val - Z₀‖ < 2 * r / Real.pi :=
    ((hval.sub (tendsto_const_nhds (x := Z₀))).norm).eventually
      (eventually_lt_nhds Z.property)
  let v : ℕ → NearCircleLittleContour Z₀ r := fun n =>
    if h : ‖(u n).val - Z₀‖ < 2 * r / Real.pi then ⟨u n, h⟩ else Z
  have hvu : u =ᶠ[atTop] fun n => (v n).val := by
    filter_upwards [hn] with n hn
    simp only [v, dif_pos hn]
  have hv : Tendsto v atTop (𝓝 Z) := tendsto_subtype_rng.mpr (hlim.congr' hvu)
  have hF : Tendsto (fun n => nearCircleSelfLogC1 hγ hγ1 Z₀ hr href (v n)) atTop
      (𝓝 (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z)) :=
    ((continuous_nearCircleSelfLogC1 hγ hγ1 Z₀ hr href).tendsto Z).comp hv
  apply (isClosed_littleContourSpace γ).mem_of_tendsto hF
  filter_upwards [hn] with n hn
  have hvn : (v n).val = u n := by simp only [v, dif_pos hn]
  apply ContourC1Space.mem_little_of_lift_eq_smooth_selfLog
    (v n).val.val (nearCircleSelfLogC1 hγ hγ1 Z₀ hr href (v n))
    (by simpa only [hvn] using hs n)
    (positiveChordConstant_pos (nearCirclePositiveContour Z₀ hr href (v n)))
    (hasChordArcLower_positiveChordConstant (nearCirclePositiveContour Z₀ hr href (v n)))
    (lift_nearCircleSelfLogC1 hγ hγ1 Z₀ hr href (v n))

/-- An actual little-space value of the literal self-log contour integral. -/
def nearCircleSelfLogLittle {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : NearCircleLittleContour Z₀ r) : LittleContourSpace γ :=
  ⟨nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z,
    nearCircleSelfLogC1_mem_little hγ hγ1 Z₀ hr href Z⟩

@[simp] theorem inclusion_nearCircleSelfLogLittle {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : NearCircleLittleContour Z₀ r) :
    LittleContourSpace.inclusion γ (nearCircleSelfLogLittle hγ hγ1 Z₀ hr href Z) =
      nearCircleSelfLogC1 hγ hγ1 Z₀ hr href Z := rfl

@[simp] theorem lift_nearCircleSelfLogLittle {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (Z : NearCircleLittleContour Z₀ r) :
    LittleContourSpace.lift γ (nearCircleSelfLogLittle hγ hγ1 Z₀ hr href Z) =
      ContourC1Space.selfLogIntegral Z.val.val := rfl

theorem continuous_nearCircleSelfLogLittle {γ : ℝ≥0}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (Z₀ : ContourC1Space γ)
    {r : ℝ} (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r) :
    Continuous (nearCircleSelfLogLittle hγ hγ1 Z₀ hr href) :=
  (continuous_nearCircleSelfLogC1 hγ hγ1 Z₀ hr href).subtype_mk _

end Euler2D

end
