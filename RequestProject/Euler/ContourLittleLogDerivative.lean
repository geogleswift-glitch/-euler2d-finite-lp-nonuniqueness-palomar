module

public import RequestProject.Euler.ContourLogDerivativeUniformLimit
public import RequestProject.Euler.ContourLogCircle
public import RequestProject.Euler.SmoothContourApproximation

/-! The original log self-interaction has its actual Hölder derivative
for little Hölder contours. The proof uses a genuinely constructed smooth
sequence, actual uniform limits, and closedness of differentiation. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ComplexConjugate ContDiff BoundedContinuousFunction

namespace Euler2D

local instance (priority := 2000) littleLog_normedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)

local instance (priority := 2000) littleLog_c1NormedAddCommGroup (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

theorem hasDerivAt_contourSelfIntegral_little_near_circle {γ : ℝ≥0}
    (Z : LittleContourSpace γ) (Z₀ : ContourC1Space γ) {c r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z.val c)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z.val - Z₀‖ < 2 * r / Real.pi) (θ : ℝ) :
    HasDerivAt
      (contourSelfIntegral (ContourC1Space.lift γ Z.val) (deriv (ContourC1Space.lift γ Z.val)))
      (contourLogDerivativeHolder Z.val hγ hγ1 hc hZ (θ : ContourCircle)) θ := by
  obtain ⟨u, hs, hu, _, hlim⟩ := LittleContourSpace.exists_smooth_chord_approximation Z hc hZ
  let v : ℕ → PositiveChordContour γ := fun n => ⟨(u n).val, ⟨c / 2, half_pos hc, hu n⟩⟩
  let v₀ : PositiveChordContour γ := ⟨Z.val, ⟨c, hc, hZ⟩⟩
  have hval : Tendsto (fun n => (u n).val) atTop (𝓝 Z.val) :=
    ((LittleContourSpace.inclusion γ).continuous.tendsto Z).comp hlim
  have hv : Tendsto v atTop (𝓝 v₀) := tendsto_subtype_rng.mpr hval
  have hd := tendstoUniformly_positiveContourLogDerivative hγ hγ1 hv
  have hfb : Tendsto (fun n => ContourC1Space.selfLogCircleBCF (v n)) atTop
      (𝓝 (ContourC1Space.selfLogCircleBCF v₀)) :=
    (ContourC1Space.continuous_selfLogCircleBCF.tendsto v₀).comp hv
  have hfu : TendstoUniformly
      (fun n => contourSelfIntegral (ContourC1Space.lift γ (u n).val)
        (deriv (ContourC1Space.lift γ (u n).val)))
      (contourSelfIntegral (ContourC1Space.lift γ Z.val) (deriv (ContourC1Space.lift γ Z.val))) atTop :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hfb).comp
      (fun t : ℝ => (t : ContourCircle))
  have hn : ∀ᶠ n in atTop, ‖(u n).val - Z₀‖ < 2 * r / Real.pi :=
    ((hval.sub (tendsto_const_nhds (x := Z₀))).norm).eventually (eventually_lt_nhds hsmall)
  have hdiff : ∀ᶠ n in atTop, ∀ t : ℝ,
      HasDerivAt
        (contourSelfIntegral (ContourC1Space.lift γ (u n).val) (deriv (ContourC1Space.lift γ (u n).val)))
        (positiveContourLogDerivativeHolder hγ hγ1 (v n) (t : ContourCircle)) t := by
    filter_upwards [hn] with n hn t
    exact hasDerivAt_contourSelfIntegral_smooth_near_circle_holder (u n).val Z₀ hγ hγ1
      (positiveChordConstant_pos (v n)) (hasChordArcLower_positiveChordConstant (v n))
      hr href hn (hs n) t
  have h := hasDerivAt_of_tendstoUniformly hd hdiff
    (fun t => TendstoUniformly.tendsto_at hfu t) θ
  rw [positiveContourLogDerivativeHolder_eq hγ hγ1 v₀ hc hZ] at h
  exact h

/-- The actual integral and its proved actual Hölder derivative give a
genuine element of the complete C¹ Hölder graph. -/
def contourSelfIntegralC1_of_little_near_circle {γ : ℝ≥0}
    (Z : LittleContourSpace γ) (Z₀ : ContourC1Space γ) {c r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z.val c)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z.val - Z₀‖ < 2 * r / Real.pi) : ContourC1Space γ :=
  ContourC1Space.ofHasDerivAt
    (ContourC1Space.selfLogCircleBCF ⟨Z.val, ⟨c, hc, hZ⟩⟩)
    (contourLogDerivativeHolder Z.val hγ hγ1 hc hZ)
    (hasDerivAt_contourSelfIntegral_little_near_circle Z Z₀ hγ hγ1 hc hZ hr href hsmall)

@[simp] theorem lift_contourSelfIntegralC1_of_little_near_circle {γ : ℝ≥0}
    (Z : LittleContourSpace γ) (Z₀ : ContourC1Space γ) {c r : ℝ}
    (hγ : 0 < (γ : ℝ)) (hγ1 : (γ : ℝ) < 1) (hc : 0 < c)
    (hZ : ContourC1Space.HasChordArcLower Z.val c)
    (hr : 0 < r) (href : ContourC1Space.lift γ Z₀ = refCircle r)
    (hsmall : ‖Z.val - Z₀‖ < 2 * r / Real.pi) :
    ContourC1Space.lift γ (contourSelfIntegralC1_of_little_near_circle Z Z₀ hγ hγ1 hc hZ hr href hsmall) =
      contourSelfIntegral (ContourC1Space.lift γ Z.val) (deriv (ContourC1Space.lift γ Z.val)) := rfl

end Euler2D

end
