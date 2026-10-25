module

public import RequestProject.Euler.ContourPhaseVorticity
public import RequestProject.Euler.ContourComplexC1Space

/-! Exact covariance of genuine radial-fill indicator densities under
nonzero complex scaling. This includes the fixed physical entry frame. -/

@[expose] public section

set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set
open scoped NNReal

namespace Euler2D

theorem mem_contourRadialFill_complex_mul_iff {a : ℂ} (ha : a ≠ 0)
    (z : ℝ → ℂ) (x : ℂ) :
    x ∈ contourRadialFill (fun θ => a * z θ) ↔ a⁻¹ * x ∈ contourRadialFill z := by
  constructor
  · rintro ⟨θ, t, ht0, ht1, hx⟩
    refine ⟨θ, t, ht0, ht1, ?_⟩
    rw [hx]
    simp only [Complex.real_smul]
    calc
      _ = (a⁻¹ * a) * ((t : ℂ) * z θ) := by ring
      _ = _ := by rw [inv_mul_cancel₀ ha, one_mul]
  · rintro ⟨θ, t, ht0, ht1, hx⟩
    refine ⟨θ, t, ht0, ht1, ?_⟩
    calc
      x = a * (a⁻¹ * x) := (mul_inv_cancel_left₀ ha x).symm
      _ = t • (a * z θ) := by rw [hx]; simp only [Complex.real_smul]; ring

theorem phaseContourPatchVorticity_complexScale {γ : ℝ≥0} {a : ℂ}
    (ha : a ≠ 0) (Z : ContourC1Space γ) (x : ℂ) :
    phaseContourPatchVorticity (ContourC1Space.complexScale a Z) x =
      phaseContourPatchVorticity Z (a⁻¹ * x) := by
  have he : ContourC1Space.lift γ (ContourC1Space.complexScale a Z) =
      fun θ => a * ContourC1Space.lift γ Z θ :=
    funext (ContourC1Space.lift_complexScale a Z)
  unfold phaseContourPatchVorticity
  rw [he]
  have hm := mem_contourRadialFill_complex_mul_iff ha (ContourC1Space.lift γ Z) x
  by_cases hx : a⁻¹ * x ∈ contourRadialFill (ContourC1Space.lift γ Z)
  · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (fun h => hx (hm.mp h)), indicator_of_notMem hx]

theorem phaseFiniteContourPatchVorticity_complexScale
    {γ : ℝ≥0} {ι : Type*} [Fintype ι] {a : ℂ} (ha : a ≠ 0)
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) (x : ℂ) :
    phaseFiniteContourPatchVorticity g (fun i => ContourC1Space.complexScale a (Z i)) x =
      phaseFiniteContourPatchVorticity g Z (a⁻¹ * x) := by
  simp only [phaseFiniteContourPatchVorticity, phaseContourPatchVorticity_complexScale ha]

end Euler2D

end
