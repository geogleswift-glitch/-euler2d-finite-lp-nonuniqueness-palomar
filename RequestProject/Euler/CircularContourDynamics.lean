module

public import RequestProject.Euler.ContourCircularBoundaryVelocity
public import RequestProject.Euler.ContourBoundaryField
public import RequestProject.Euler.CircularCell

/-! The reference circular cell satisfies the literal material contour
equation. Its angular velocities and period are derived from the
actual boundary integrals, rather than from an assumed circulation law. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory

namespace Euler2D

def circularContourRadii : Fin 2 → ℝ := ![cellA, 1]
def circularContourStrengths : Fin 2 → ℝ := ![5 / 2, -3 / 2]
def circularContourAngularVelocities : Fin 2 → ℝ := ![1 / 2, 0]

theorem contourBoundaryField_refCircles {ι : Type*} [Fintype ι]
    (g r : ι → ℝ) (hr : ∀ i, 0 < r i) (i : ι) (θ : ℝ) :
    contourBoundaryField g (fun j => refCircle (r j)) i θ =
      ∑ j, (g j : ℂ) * (I * (((r j / 2 * (min (r i) (r j) / max (r i) (r j)) : ℝ) : ℂ)) *
        exp ((θ : ℂ) * I)) := by
  unfold contourBoundaryField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (g j : ℂ) * ((-1 / (2 * Real.pi) : ℂ) *
      contourLogBoundaryIntegral (refCircle (r j)) (deriv (refCircle (r j))) (refCircle (r i) θ)) := by ring
    _ = _ := by rw [contourCircular_patchBoundaryVelocity (hr i) (hr j) θ]

theorem circularContour_reference_field (i : Fin 2) (θ : ℝ) :
    contourBoundaryField circularContourStrengths
      (fun j => refCircle (circularContourRadii j)) i θ =
      (circularContourAngularVelocities i : ℂ) * I * refCircle (circularContourRadii i) θ := by
  have hr : ∀ i, 0 < circularContourRadii i := by
    intro j
    fin_cases j <;> simp [circularContourRadii, cellA_pos]
  rw [contourBoundaryField_refCircles circularContourStrengths circularContourRadii hr]
  have ha := cellA_pos
  have ha1 := cellA_lt_one.le
  have ha2 := congrArg Complex.ofReal cellA_sq
  push_cast at ha2
  fin_cases i
  · norm_num [Fin.sum_univ_two, circularContourStrengths, circularContourRadii,
      circularContourAngularVelocities, min_eq_left ha1, max_eq_right ha1, ha.ne', refCircle]
    push_cast
    ring
  · norm_num [Fin.sum_univ_two, circularContourStrengths, circularContourRadii,
      circularContourAngularVelocities, min_eq_right ha1, max_eq_left ha1, refCircle]
    push_cast
    ring_nf
    rw [ha2]
    ring

theorem contourBoundaryField_reparametrize {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (z : ι → ℝ → ℂ) (b : ι → ℝ)
    (hz : ∀ j, Differentiable ℝ (z j))
    (hp : ∀ j, Function.Periodic (z j) (2 * Real.pi))
    (hpd : ∀ j, Function.Periodic (deriv (z j)) (2 * Real.pi)) (i : ι) (θ : ℝ) :
    contourBoundaryField g (fun j φ => z j (φ + b j)) i θ =
      contourBoundaryField g z i (θ + b i) := by
  have hd (j : ι) : deriv (fun φ => z j (φ + b j)) = fun φ => deriv (z j) (φ + b j) := by
    funext φ
    have h := ((hz j (φ + b j)).hasDerivAt).scomp φ ((hasDerivAt_id φ).add_const (b j))
    simpa only [Function.comp_def, one_smul] using h.deriv
  unfold contourBoundaryField
  simp_rw [hd]
  apply congrArg ((-1 / (2 * Real.pi) : ℂ) * ·)
  apply Finset.sum_congr rfl
  intro j _
  rw [contourLogBoundaryIntegral_comp_add (z j) (deriv (z j)) (hp j) (hpd j)]

def circularMaterialContours (t : ℝ) (i : Fin 2) (θ : ℝ) : ℂ :=
  refCircle (circularContourRadii i) (θ + circularContourAngularVelocities i * t)

theorem circularMaterialContours_hasDerivAt (t : ℝ) (i : Fin 2) (θ : ℝ) :
    HasDerivAt (fun s => circularMaterialContours s i θ)
      (contourBoundaryField circularContourStrengths (circularMaterialContours t) i θ) t := by
  have hz (j : Fin 2) : Differentiable ℝ (refCircle (circularContourRadii j)) :=
    (contDiff_refCircle _).differentiable (by norm_num)
  have hpd (j : Fin 2) : Function.Periodic (deriv (refCircle (circularContourRadii j)))
      (2 * Real.pi) := by
    rw [deriv_refCircle]
    intro φ
    dsimp only
    have hp := periodic_contourCircleCharacter 1 φ
    simp only [contourCircleCharacter, Int.cast_one, one_mul] at hp
    rw [hp]
  change HasDerivAt (fun s => refCircle (circularContourRadii i)
    (θ + circularContourAngularVelocities i * s))
    (contourBoundaryField circularContourStrengths
      (fun j φ => refCircle (circularContourRadii j) (φ + circularContourAngularVelocities j * t)) i θ) t
  rw [contourBoundaryField_reparametrize
    circularContourStrengths (fun j => refCircle (circularContourRadii j))
    (fun j => circularContourAngularVelocities j * t) hz (fun j => periodic_refCircle _) hpd,
    circularContour_reference_field]
  have hd := (hasDerivAt_refCircle (circularContourRadii i)
    (θ + circularContourAngularVelocities i * t)).scomp t
      ((hasDerivAt_const t θ).add ((hasDerivAt_id t).const_mul (circularContourAngularVelocities i)))
  convert hd using 1 <;> simp only [Function.comp_def, zero_add, Complex.real_smul, refCircle] <;> ring

theorem circularMaterialContours_period (i : Fin 2) (θ : ℝ) :
    circularMaterialContours period i θ = circularMaterialContours 0 i θ := by
  fin_cases i
  · norm_num [circularMaterialContours, circularContourAngularVelocities]
    have he : (1 / 2 : ℝ) * period = 2 * Real.pi := by unfold period; ring
    rw [he, periodic_refCircle]
  · simp [circularMaterialContours, circularContourAngularVelocities]

end Euler2D

end
