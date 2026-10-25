module

public import RequestProject.Euler.CircularProjectedExteriorForcing
public import RequestProject.Euler.ComplexRotatingDensityNormalization

/-! The leading growing-coordinate decomposition in the actual
amplitude, length and rotating physical coordinates. The returned
contour field is the normalized original volume velocity. -/

@[expose] public section

set_option maxHeartbeats 18000000
set_option maxRecDepth 7000

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ComplexConjugate

namespace Euler2D

local instance (priority := 2000) normalizedProjectedLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) normalizedProjectedLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem exists_circular_normalized_source_forcing_with_projection {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) ≤ 1) {w : ℂ → ℝ} {S B amp r d ε : ℝ}
    (hamp : 0 < amp) (hr : 0 < r) (θ : ℝ)
    (hS : 0 ≤ S) (hw : Integrable w) (hsupp : ∀ z, S < ‖z‖ → w z = 0)
    (hmass : ∫ z, w z = 0) (hsym : ∀ z, w (I * z) = w z)
    (hB : (∫ z : ℂ, |w z|) ≤ B) (hd : 0 < d) (hdref : d ≤ cellA) (hsep : 8 * (S / r) ≤ d)
    (Z : Fin 2 → LittleContourSpace γ)
    (hZ : ∀ i x, d ≤ ‖ContourC1Space.toBCF γ (Z i).val x‖)
    (hnear : ∀ i u, ‖LittleContourSpace.lift γ (Z i) u - refCircle (circularContourRadii i) u‖ ≤ ε) :
    ∃ Q : Fin 2 → LittleContourSpace γ,
      (∀ i u, LittleContourSpace.lift γ (Q i) u =
        Complex.exp (-((θ : ℂ) * I)) * ((amp * r)⁻¹ •
          velocityC w (r • (Complex.exp ((θ : ℂ) * I) * LittleContourSpace.lift γ (Z i) u)))) ∧
      ‖circularUnstableCoordinateCLM γ Q - Kstar *
        ((amp⁻¹ : ℂ) * (r⁻¹ : ℂ) ^ 6 * Complex.exp (4 * (θ : ℂ) * I) * momentN w 4)‖ ≤
        (2 / cellA) * (8 / (15 * Real.pi) * ((S / r) ^ 8 * (amp⁻¹ * r⁻¹ ^ 2 * B)) / d ^ 9 +
          (5 / (2 * Real.pi * d ^ 6)) * ((S / r) ^ 4 * (amp⁻¹ * r⁻¹ ^ 2 * B)) * ε) := by
  let wn := normalizedRotatingComplexDensity amp r θ w
  have hSn : 0 ≤ S / r := div_nonneg hS hr.le
  have hwn : Integrable wn := integrable_normalizedRotatingComplexDensity hw amp θ hr
  have hsuppn : ∀ z, S / r < ‖z‖ → wn z = 0 :=
    normalizedRotatingComplexDensity_support hsupp hr amp θ
  have hmassn : (∫ z, wn z) = 0 := by
    simpa only [hmass, mul_zero] using integral_normalizedRotatingComplexDensity amp θ hr w
  have hsymn : ∀ z, wn (I * z) = wn z := normalizedRotatingComplexDensity_fourfold hsym amp r θ
  have hBn : (∫ z : ℂ, |wn z|) ≤ amp⁻¹ * r⁻¹ ^ 2 * B :=
    (integral_abs_normalizedRotatingComplexDensity hamp hr θ w).trans_le
      (mul_le_mul_of_nonneg_left hB (mul_nonneg (inv_pos.mpr hamp).le (by positivity)))
  obtain ⟨Q, hQ, hprojection⟩ := exists_circular_source_forcing_with_multipole_projection hγ hγ1
    hSn hwn hsuppn hmassn hsymn hBn hd hdref hsep Z hZ hnear
  refine ⟨Q, ?_, ?_⟩
  · intro i u
    exact (hQ i u).trans
      (velocityC_normalizedRotatingComplexDensity hamp hr θ w (LittleContourSpace.lift γ (Z i) u))
  · change ‖circularUnstableCoordinateCLM γ Q - Kstar *
      momentN (normalizedRotatingComplexDensity amp r θ w) 4‖ ≤ _ at hprojection
    rw [momentN_normalizedRotatingComplexDensity_fourth amp θ hr w] at hprojection
    exact hprojection

end Euler2D

end
