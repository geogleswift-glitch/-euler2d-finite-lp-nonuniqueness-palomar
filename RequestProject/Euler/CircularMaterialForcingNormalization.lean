module

public import RequestProject.Euler.CircularCanonicalAbsoluteGauge
public import RequestProject.Euler.LittleContourComplexScalar

/-! Exact inverse amplitude/length/rotation/parameter normalization
for the actual material forcing. A normalized source along the
materially unshifted target reconstructs a literal raw physical source,
and its original normalized derivative source unshifts back to Q. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) materialForceNormLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) materialForceNormLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

def materialPhysicalForcing {γ : ℝ≥0} (A r θ : ℝ) (β : Fin 2 → ℝ)
    (Q : Fin 2 → LittleContourSpace γ) : Fin 2 → LittleContourSpace γ :=
  (A * r) • (Complex.exp ((θ : ℂ) * I) • contourParameterShiftFamilyCLM γ β Q)

theorem materialPhysicalForcing_lift {γ : ℝ≥0} {A r : ℝ}
    (hA : A ≠ 0) (hr : r ≠ 0) (θ : ℝ) (β : Fin 2 → ℝ)
    (raw Z Q : Fin 2 → LittleContourSpace γ) (V : ℂ → ℂ)
    (hraw : r • (Complex.exp ((θ : ℂ) * I) • contourParameterShiftFamilyCLM γ β Z) = raw)
    (hQ : ∀ i u, LittleContourSpace.lift γ (Q i) u =
      Complex.exp (-((θ : ℂ) * I)) * ((A * r)⁻¹ •
        V (r • (Complex.exp ((θ : ℂ) * I) * LittleContourSpace.lift γ (Z i) u)))) :
    ∀ i u, LittleContourSpace.lift γ (materialPhysicalForcing A r θ β Q i) u =
      V (LittleContourSpace.lift γ (raw i) u) := by
  have hAr : A * r ≠ 0 := mul_ne_zero hA hr
  have hcancel : Complex.exp ((θ : ℂ) * I) * Complex.exp (-((θ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hpoint (i : Fin 2) (u : ℝ) :
      r • (Complex.exp ((θ : ℂ) * I) * LittleContourSpace.lift γ (Z i) (u + β i)) =
        LittleContourSpace.lift γ (raw i) u := by
    have hh := congrArg (fun W : Fin 2 → LittleContourSpace γ => LittleContourSpace.lift γ (W i) u) hraw
    exact hh
  intro i u
  change (A * r) • (Complex.exp ((θ : ℂ) * I) *
    LittleContourSpace.lift γ (Q i) (u + β i)) = _
  rw [hQ, hpoint]
  simp only [Complex.real_smul]
  rw [← mul_assoc (Complex.exp ((θ : ℂ) * I)) (Complex.exp (-((θ : ℂ) * I))),
    hcancel, one_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hAr,
    Complex.ofReal_one, one_mul]

theorem materialPhysicalForcing_unshift_normalized {γ : ℝ≥0} {A r : ℝ}
    (hA : A ≠ 0) (hr : r ≠ 0) (θ : ℝ) (β : Fin 2 → ℝ) (Q : Fin 2 → LittleContourSpace γ) :
    contourParameterShiftFamilyCLM γ (-β)
      (Complex.exp (-((θ : ℂ) * I)) • ((A * r)⁻¹ • materialPhysicalForcing A r θ β Q)) = Q := by
  have hAr : A * r ≠ 0 := mul_ne_zero hA hr
  have hcancel : Complex.exp (-((θ : ℂ) * I)) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  funext i
  apply Subtype.ext
  apply ContourC1Space.ext
  intro x
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  change Complex.exp (-((θ : ℂ) * I)) *
    ((A * r)⁻¹ • ((A * r) • (Complex.exp ((θ : ℂ) * I) *
      LittleContourSpace.lift γ (Q i) ((u + -β i) + β i)))) = LittleContourSpace.lift γ (Q i) u
  rw [show (u + -β i) + β i = u by ring, inv_smul_smul₀ hAr,
    ← mul_assoc, hcancel, one_mul]

end Euler2D

end
