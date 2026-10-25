module

public import RequestProject.Euler.ContourChordArc
public import RequestProject.Euler.ContourLogKernel

/-!
# Continuity of actual logarithmic contour integrals

The integration variable is the relative angle.  A genuine positive chord
bound excludes a collision away from the one null parameter `τ = 0`.
The dominated convergence theorem then applies to the literal logarithmic
integrand, with a common integrable bound.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real MeasureTheory
open scoped Interval

namespace Euler2D

variable {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]

/-- Joint continuity of the actual self-contour integral, from a genuine
short-arc chord bound and a common integrable dominator. -/
theorem continuous_contourLogSelfIntegral_of_domination
    (z dz : A → ℝ → ℂ) (c : ℝ) (B : ℝ → ℝ)
    (hz : Continuous (Function.uncurry z))
    (hdz : Continuous (Function.uncurry dz)) (hc : 0 < c)
    (hchord : ∀ a θ τ, |τ| ≤ π → c * |τ| ≤ ‖z a θ - z a (θ + τ)‖)
    (hB : IntervalIntegrable B volume (-π) π)
    (hbound : ∀ a θ τ, |τ| ≤ π → τ ≠ 0 →
      ‖Real.log ‖z a θ - z a (θ + τ)‖ • dz a (θ + τ)‖ ≤ B τ) :
    Continuous (fun q : A × ℝ =>
      ∫ τ in (-π)..π, Real.log ‖z q.1 q.2 - z q.1 (q.2 + τ)‖ • dz q.1 (q.2 + τ)) := by
  have hmeas (q : A × ℝ) : AEStronglyMeasurable
      (fun τ : ℝ => Real.log ‖z q.1 q.2 - z q.1 (q.2 + τ)‖ • dz q.1 (q.2 + τ))
      (volume.restrict (Ι (-π) π)) := by
    have hzτ : Continuous (fun τ : ℝ => z q.1 q.2 - z q.1 (q.2 + τ)) :=
      continuous_const.sub (hz.comp (continuous_const.prodMk (continuous_const.add continuous_id)))
    have hdτ : Continuous (fun τ : ℝ => dz q.1 (q.2 + τ)) :=
      hdz.comp (continuous_const.prodMk (continuous_const.add continuous_id))
    exact (hzτ.norm.measurable.log.smul hdτ.measurable).aestronglyMeasurable
  have hangle {τ : ℝ} (hτ : τ ∈ Ι (-π) π) : |τ| ≤ π := by
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -π ≤ π)] at hτ
    exact abs_le.mpr ⟨hτ.1.le, hτ.2⟩
  refine intervalIntegral.continuous_of_dominated_interval hmeas ?_ hB ?_
  · intro q
    filter_upwards [volume.ae_ne (0 : ℝ)] with τ hτ
    intro hmem
    exact hbound q.1 q.2 τ (hangle hmem) hτ
  · filter_upwards [volume.ae_ne (0 : ℝ)] with τ hτ
    intro hmem
    have hzshift : Continuous (fun q : A × ℝ => z q.1 (q.2 + τ)) :=
      hz.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hdshift : Continuous (fun q : A × ℝ => dz q.1 (q.2 + τ)) :=
      hdz.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hn (q : A × ℝ) : ‖z q.1 q.2 - z q.1 (q.2 + τ)‖ ≠ 0 := by
      have hp : 0 < c * |τ| := mul_pos hc (abs_pos.mpr hτ)
      exact ne_of_gt (hp.trans_le (hchord q.1 q.2 τ (hangle hmem)))
    exact ((hz.sub hzshift).norm.log hn).smul hdshift

/-- The actual logarithmic contour integral depends jointly continuously
on its curve parameter and its evaluation angle.  The common dominator
is obtained from the explicit curve, derivative, and chord bounds. -/
theorem continuous_contourSelfIntegral
    (z dz : A → ℝ → ℂ) {c M D : ℝ}
    (hz : Continuous (Function.uncurry z))
    (hdz : Continuous (Function.uncurry dz)) (hc : 0 < c)
    (hM : ∀ a t, ‖z a t‖ ≤ M) (hD : ∀ a t, ‖dz a t‖ ≤ D)
    (hca : ∀ a θ τ, |τ| ≤ π → c * |τ| ≤ ‖z a θ - z a (θ + τ)‖) :
    Continuous (fun q : A × ℝ => contourSelfIntegral (z q.1) (dz q.1) q.2) := by
  have h := continuous_contourLogSelfIntegral_of_domination z dz c
    (fun τ => D * contourLogMajorant c M τ) hz hdz hc hca
    ((intervalIntegrable_contourLogMajorant c M).const_mul D) (by
      intro a θ τ hτ _
      change ‖contourSelfIntegrand (z a) (dz a) θ τ‖ ≤ D * contourLogMajorant c M τ
      exact norm_contourSelfIntegrand_le hc (hM a) (hD a) (hca a) θ τ hτ)
  simpa only [contourSelfIntegral, contourSelfIntegrand, contourLogIntegrand] using h

/-- In particular, the true self-contour integral is continuous in its
evaluation angle for a fixed admissible curve and its derivative. -/
theorem continuous_contourSelfIntegral_fixed {z dz : ℝ → ℂ} {c M D : ℝ}
    (hz : Continuous z) (hdz : Continuous dz) (hc : 0 < c)
    (hM : ∀ t, ‖z t‖ ≤ M) (hD : ∀ t, ‖dz t‖ ≤ D)
    (hca : ∀ θ τ, |τ| ≤ π → c * |τ| ≤ ‖z θ - z (θ + τ)‖) :
    Continuous (contourSelfIntegral z dz) := by
  have h := continuous_contourSelfIntegral (fun _ : Unit => z) (fun _ : Unit => dz)
    (hz.comp continuous_snd) (hdz.comp continuous_snd) hc (fun _ => hM) (fun _ => hD)
    (fun _ => hca)
  have hpair : Continuous (fun θ : ℝ => ((() : Unit), θ)) :=
    continuous_const.prodMk continuous_id
  exact h.comp hpair

end Euler2D

end
