module

public import RequestProject.Euler.ContourC1PatchVelocity
public import RequestProject.Euler.ContourDomainFill

/-! Spatial rotation of the original field, and fourfold invariance of
the actual enclosed patches, derived from the original actual loops. -/

@[expose] public section

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal

namespace Euler2D

theorem contourBoundaryField_mul_unit {ι : Type*} [Fintype ι] (g : ι → ℝ)
    (z : ι → ℝ → ℂ) (hz : ∀ j, Differentiable ℝ (z j)) {a : ℂ}
    (ha : ‖a‖ = 1) (i : ι) (θ : ℝ) :
    contourBoundaryField g (fun j φ => a * z j φ) i θ = a * contourBoundaryField g z i θ := by
  have hd (j : ι) : deriv (fun φ => a * z j φ) = fun φ => a * deriv (z j) φ := by
    funext φ
    exact (((hz j φ).hasDerivAt).const_mul a).deriv
  have hB (j : ι) : contourLogBoundaryIntegral (fun φ => a * z j φ)
      (deriv (fun φ => a * z j φ)) (a * z i θ) =
      a * contourLogBoundaryIntegral (z j) (deriv (z j)) (z i θ) := by
    rw [hd j]
    exact contourLogBoundaryIntegral_mul_unit _ _ ha _
  unfold contourBoundaryField
  simp_rw [hB]
  calc
    _ = (-1 / (2 * Real.pi) : ℂ) * ∑ j,
        a * ((g j : ℂ) * contourLogBoundaryIntegral (z j) (deriv (z j)) (z i θ)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem contourRadialFill_rotShift (z : ℝ → ℂ) (b : ℝ) :
    contourRadialFill (rotShift b z) =
      (fun x : ℂ => exp ((b : ℂ) * I) * x) '' contourRadialFill z := by
  apply Set.Subset.antisymm
  · rintro x ⟨θ, t, ht0, ht1, rfl⟩
    refine ⟨t • z (θ - b), ⟨θ - b, t, ht0, ht1, rfl⟩, ?_⟩
    simp only [rotShift, Complex.real_smul]
    ring
  · rintro x ⟨y, ⟨θ, t, ht0, ht1, rfl⟩, rfl⟩
    refine ⟨θ + b, t, ht0, ht1, ?_⟩
    simp only [rotShift, add_sub_cancel_right, Complex.real_smul]
    ring

theorem contourC1EnclosedDomain_mul_I_iff {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (hsmall : ‖Z - Z₀‖ ≤ r / 4)
    (hrot : ∀ θ, ContourC1Space.lift γ Z (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ Z θ) (x : ℂ) :
    I * x ∈ contourC1EnclosedDomain Z Z₀ hr href hsmall ↔
      x ∈ contourC1EnclosedDomain Z Z₀ hr href hsmall := by
  have hD : contourC1EnclosedDomain Z Z₀ hr href hsmall =
      contourRadialFill (ContourC1Space.lift γ Z) :=
    nearCircleEnclosedDomain_eq_contourRadialFill hr (norm_nonneg _) hsmall
      (fun θ => (ContourC1Space.hasDerivAt_lift Z θ).differentiableAt.hasDerivAt)
      (contourC1_norm_sub_ref_le Z Z₀ href) (contourC1_norm_deriv_sub_ref_le Z Z₀ href)
      (ContourC1Space.periodic_lift Z)
  rw [hD]
  exact mul_I_mem_contourRadialFill_iff hrot x

theorem contourC1PatchVorticity_mul_I {γ : ℝ≥0}
    (Z Z₀ : ContourC1Space γ) {r : ℝ} (hr : 0 < r)
    (href : ContourC1Space.lift γ Z₀ = refCircle r) (hsmall : ‖Z - Z₀‖ ≤ r / 4)
    (hrot : ∀ θ, ContourC1Space.lift γ Z (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ Z θ) (x : ℂ) :
    contourC1PatchVorticity Z Z₀ hr href hsmall (I * x) =
      contourC1PatchVorticity Z Z₀ hr href hsmall x := by
  have hiff := contourC1EnclosedDomain_mul_I_iff Z Z₀ hr href hsmall hrot x
  by_cases hx : x ∈ contourC1EnclosedDomain Z Z₀ hr href hsmall
  · simp [contourC1PatchVorticity, hx, hiff.mpr hx]
  · have hn : I * x ∉ contourC1EnclosedDomain Z Z₀ hr href hsmall := mt hiff.mp hx
    simp [contourC1PatchVorticity, hx, hn]

theorem finiteContourC1PatchVorticity_mul_I {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (r : ι → ℝ)
    (hr : ∀ j, 0 < r j) (href : ∀ j, ContourC1Space.lift γ (Z₀ j) = refCircle (r j))
    (hsmall : ∀ j, ‖Z j - Z₀ j‖ ≤ r j / 4)
    (hrot : ∀ j θ, ContourC1Space.lift γ (Z j) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z j) θ) (x : ℂ) :
    finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall (I * x) =
      finiteContourC1PatchVorticity g Z Z₀ r hr href hsmall x := by
  unfold finiteContourC1PatchVorticity
  apply Finset.sum_congr rfl
  intro j _
  rw [contourC1PatchVorticity_mul_I (Z j) (Z₀ j) (hr j) (href j) (hsmall j) (hrot j)]

end Euler2D
