module

public import RequestProject.Euler.ContourChordArc
public import RequestProject.Euler.ContourC1Space

/-!
# Stability and openness of genuine positive chord bounds

These predicates describe only the actual quantitative chord bound.  No
orientation or choice of an interior is part of the definition.
-/

@[expose] public section

noncomputable section

open Complex Set Filter Topology Metric Real
open scoped ContDiff NNReal

namespace Euler2D

/-- Stability of a genuine chord bound under a perturbation whose actual
derivative is uniformly small. -/
theorem chord_lower_of_deriv_difference_bound
    {z z₀ : ℝ → ℂ} {c ε θ φ : ℝ}
    (hp : ContDiff ℝ 1 (fun t => z t - z₀ t)) (hε : 0 ≤ ε)
    (hderiv : ∀ t, ‖deriv (fun s => z s - z₀ s) t‖ ≤ ε)
    (hbase : c * |θ - φ| ≤ ‖z₀ θ - z₀ φ‖) :
    (c - ε) * |θ - φ| ≤ ‖z θ - z φ‖ := by
  have hpbound := norm_sub_le_of_contDiff_deriv_bound hp hε hderiv θ φ
  have he : z₀ θ - z₀ φ = (z θ - z φ) - ((z θ - z₀ θ) - (z φ - z₀ φ)) := by abel
  have htri := norm_sub_le (z θ - z φ) ((z θ - z₀ θ) - (z φ - z₀ φ))
  rw [← he] at htri
  nlinarith

namespace ContourC1Space

variable {γ : ℝ≥0}

/-- A true uniform short-arc lower bound for the actual periodic lift. -/
def HasChordArcLower (f : ContourC1Space γ) (c : ℝ) : Prop :=
  ∀ θ τ : ℝ, |τ| ≤ π → c * |τ| ≤ ‖lift γ f θ - lift γ f (θ + τ)‖

/-- Existence of a positive genuine chord lower bound. -/
def HasPositiveChordArc (f : ContourC1Space γ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ HasChordArcLower f c

theorem hasChordArcLower_of_norm_sub (f g : ContourC1Space γ) {c : ℝ}
    (hg : HasChordArcLower g c) : HasChordArcLower f (c - ‖f - g‖) := by
  intro θ τ hτ
  have hp : ContDiff ℝ 1 (fun t => lift γ f t - lift γ g t) :=
    (contDiff_lift f).sub (contDiff_lift g)
  have hd (t : ℝ) : ‖deriv (fun s => lift γ f s - lift γ g s) t‖ ≤ ‖f - g‖ := by
    simpa only [lift_sub, Pi.sub_def] using norm_deriv_lift_le (f - g) t
  have hgap : |θ - (θ + τ)| = |τ| := by
    rw [show θ - (θ + τ) = -τ by ring, abs_neg]
  have hb := chord_lower_of_deriv_difference_bound hp (norm_nonneg (f - g)) hd
    (θ := θ) (φ := θ + τ) (c := c) (by
      simpa only [hgap] using hg θ τ hτ)
  simpa only [hgap] using hb

theorem hasChordArcLower_mono (f : ContourC1Space γ) {c d : ℝ}
    (hf : HasChordArcLower f c) (hd : d ≤ c) : HasChordArcLower f d := by
  intro θ τ hτ
  exact (mul_le_mul_of_nonneg_right hd (abs_nonneg τ)).trans (hf θ τ hτ)

theorem hasChordArcLower_of_mem_ball (f g : ContourC1Space γ) {c : ℝ}
    (hg : HasChordArcLower g c) (hfg : f ∈ Metric.ball g (c / 2)) :
    HasChordArcLower f (c / 2) := by
  apply hasChordArcLower_mono f (hasChordArcLower_of_norm_sub f g hg)
  have hn : ‖f - g‖ < c / 2 := by
    rw [← _root_.dist_eq_norm f g]
    exact hfg
  linarith

/-- Quantitative chord regularity is an open condition in the actual
closed-derivative-graph norm. -/
theorem isOpen_hasPositiveChordArc (γ : ℝ≥0) :
    IsOpen {f : ContourC1Space γ | HasPositiveChordArc f} := by
  rw [Metric.isOpen_iff]
  intro g hg
  obtain ⟨c, hc, hgc⟩ := hg
  refine ⟨c / 2, by positivity, ?_⟩
  intro f hf
  exact ⟨c / 2, by positivity, hasChordArcLower_of_mem_ball f g hgc hf⟩

end ContourC1Space

end Euler2D

end
