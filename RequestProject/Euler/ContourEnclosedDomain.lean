module

public import RequestProject.Euler.ContourStarAngle
public import RequestProject.Euler.StarDomainGeometry

/-! An actual enclosed domain constructed from the angle inverse of a
small C¹ perturbation of a circle. Its frontier is proved to be exactly
the image of the original parametrized curve. -/

@[expose] public section

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate NNReal

namespace Euler2D

def contourRadialProfile (z : ℝ → ℂ) (e : ℝ ≃o ℝ) (φ : ℝ) : ℝ :=
  ‖z (e.symm φ)‖

theorem continuous_contourRadialProfile {z : ℝ → ℂ} (hz : Continuous z) (e : ℝ ≃o ℝ) :
    Continuous (contourRadialProfile z e) := (hz.comp e.symm.continuous).norm

theorem angleOrderIso_symm_add_period {e : ℝ ≃o ℝ} {P : ℝ}
    (he : ∀ θ, e (θ + P) = e θ + P) (φ : ℝ) :
    e.symm (φ + P) = e.symm φ + P := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

theorem periodic_contourRadialProfile {z : ℝ → ℂ} {e : ℝ ≃o ℝ}
    (hp : Function.Periodic z (2 * Real.pi))
    (he : ∀ θ, e (θ + 2 * Real.pi) = e θ + 2 * Real.pi) :
    Function.Periodic (contourRadialProfile z e) (2 * Real.pi) := by
  intro φ
  simp only [contourRadialProfile, angleOrderIso_symm_add_period he]
  rw [hp (e.symm φ)]

theorem radialGraph_range_eq_contour_range {z : ℝ → ℂ} {e : ℝ ≃o ℝ}
    (hpolar : ∀ θ, (‖z θ‖ : ℂ) * exp ((e θ : ℂ) * I) = z θ) :
    Set.range (fun φ : ℝ => (contourRadialProfile z e φ : ℂ) * exp ((φ : ℂ) * I)) =
      Set.range z := by
  apply Set.Subset.antisymm
  · rintro x ⟨φ, rfl⟩
    refine ⟨e.symm φ, ?_⟩
    simpa only [e.apply_symm_apply, contourRadialProfile] using (hpolar (e.symm φ)).symm
  · rintro x ⟨θ, rfl⟩
    refine ⟨e θ, ?_⟩
    simpa only [contourRadialProfile, e.symm_apply_apply] using hpolar θ

section NearCircle

variable {z dz : ℝ → ℂ} {r ε : ℝ}
  (hr : 0 < r) (hε : 0 ≤ ε) (hsmall : ε ≤ r / 4)
  (hz : ∀ θ, HasDerivAt z (dz θ) θ)
  (hv : ∀ θ, ‖z θ - refCircle r θ‖ ≤ ε)
  (hd : ∀ θ, ‖dz θ - deriv (refCircle r) θ‖ ≤ ε)

/-- The actual radial function obtained by inverting the constructed angle. -/
def nearCircleRadialProfile : ℝ → ℝ :=
  contourRadialProfile z (contourAngleOrderIso hr hε hsmall hz hv hd)

include hr hε hsmall hz hv hd

theorem continuous_nearCircleRadialProfile :
    Continuous (nearCircleRadialProfile hr hε hsmall hz hv hd) :=
  continuous_contourRadialProfile
    (continuous_iff_continuousAt.mpr (fun θ => (hz θ).continuousAt)) _

theorem nearCircleRadialProfile_bounds (φ : ℝ) :
    r - ε ≤ nearCircleRadialProfile hr hε hsmall hz hv hd φ ∧
      nearCircleRadialProfile hr hε hsmall hz hv hd φ ≤ r + ε :=
  norm_contour_sub_ref_bounds hr.le (hv _)

theorem periodic_nearCircleRadialProfile (hp : Function.Periodic z (2 * Real.pi)) :
    Function.Periodic (nearCircleRadialProfile hr hε hsmall hz hv hd) (2 * Real.pi) :=
  periodic_contourRadialProfile hp (contourAngleLift_add_period hp r)

theorem nearCircleRadialGraph_range :
    Set.range (fun φ : ℝ => (nearCircleRadialProfile hr hε hsmall hz hv hd φ : ℂ) *
      exp ((φ : ℂ) * I)) = Set.range z :=
  radialGraph_range_eq_contour_range (contour_polar_decomposition hr)

/-- A genuine open domain, defined directly from the actual curve's angle inverse. -/
def nearCircleEnclosedDomain : Set ℂ :=
  starDomain (nearCircleRadialProfile hr hε hsmall hz hv hd)

theorem isOpen_nearCircleEnclosedDomain (hp : Function.Periodic z (2 * Real.pi)) :
    IsOpen (nearCircleEnclosedDomain hr hε hsmall hz hv hd) :=
  isOpen_starDomain (continuous_nearCircleRadialProfile hr hε hsmall hz hv hd)
    (periodic_nearCircleRadialProfile hr hε hsmall hz hv hd hp)
    (show 0 < r - ε by linarith) (fun φ => (nearCircleRadialProfile_bounds hr hε hsmall hz hv hd φ).1)

/-- The original loop, with its original parametrization, is exactly the frontier. -/
theorem frontier_nearCircleEnclosedDomain (hp : Function.Periodic z (2 * Real.pi)) :
    frontier (nearCircleEnclosedDomain hr hε hsmall hz hv hd) = Set.range z := by
  change frontier (starDomain _) = _
  rw [frontier_starDomain_eq_range
    (continuous_nearCircleRadialProfile hr hε hsmall hz hv hd)
    (periodic_nearCircleRadialProfile hr hε hsmall hz hv hd hp)
    (show 0 < r - ε by linarith)
    (fun φ => (nearCircleRadialProfile_bounds hr hε hsmall hz hv hd φ).1)]
  exact nearCircleRadialGraph_range hr hε hsmall hz hv hd

theorem nearCircleEnclosedDomain_subset_ball :
    nearCircleEnclosedDomain hr hε hsmall hz hv hd ⊆ Metric.ball 0 (r + ε) :=
  starDomain_subset_ball (fun φ => (nearCircleRadialProfile_bounds hr hε hsmall hz hv hd φ).2)

theorem ball_subset_nearCircleEnclosedDomain :
    Metric.ball 0 (r - ε) ⊆ nearCircleEnclosedDomain hr hε hsmall hz hv hd := by
  intro x hx
  change ‖x‖ < nearCircleRadialProfile hr hε hsmall hz hv hd (arg x)
  exact (mem_ball_zero_iff.mp hx).trans_le
    (nearCircleRadialProfile_bounds hr hε hsmall hz hv hd _).1

theorem area_nearCircleEnclosedDomain_radial :
    volume.real (nearCircleEnclosedDomain hr hε hsmall hz hv hd) =
      ∫ φ in Ioo (-Real.pi) Real.pi,
        nearCircleRadialProfile hr hε hsmall hz hv hd φ ^ 2 / 2 :=
  area_starDomain (continuous_nearCircleRadialProfile hr hε hsmall hz hv hd)
    (fun φ => (show 0 < r - ε by linarith).trans_le
      (nearCircleRadialProfile_bounds hr hε hsmall hz hv hd φ).1)

end NearCircle

end Euler2D
