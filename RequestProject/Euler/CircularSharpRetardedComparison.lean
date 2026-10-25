module

public import RequestProject.Euler.LinearForcedHistory
public import RequestProject.Euler.CircularShiftedRetardedComparison

/-! The ORIGINAL retarded response admits finite-window comparison
with the sharp real growth rate b*sigma. The entrance discrepancy
is kept literal, and no continuity of a selected residual is needed. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem dist_shiftedRetardedTransfer_sharp_le_of_forced_equation
    {b ρ θp θc s a d ε : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (hε : 0 ≤ ε)
    (W : ℝ → ℂ)
    (hW : ∀ τ ∈ Icc a d, ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt W (((b : ℂ) * lamStar) * W τ +
        (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
          Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) * P.moment (s + τ) + E) τ) :
    ∀ τ ∈ Icc a d,
      ‖W τ - P.shiftedRetardedTransfer b ρ θp θc s τ‖ ≤
        (‖W a - P.shiftedRetardedTransfer b ρ θp θc s a‖ + ε * (τ - a)) *
          Real.exp (b * sigma * (τ - a)) := by
  let c := (b : ℂ) * lamStar
  let R := P.shiftedRetardedTransfer b ρ θp θc s
  have hc : c.re = b * sigma := by dsimp only [c]; simp [lamStar]
  have hc0 : 0 ≤ c.re := by rw [hc]; exact mul_nonneg hb.1.le sigma_pos.le
  intro τ hτ
  let Z := fun u : ℝ => W (a + u) - R (a + u)
  have hZE : ∀ u ∈ Icc (0 : ℝ) (τ - a), ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt Z (c * Z u + E) u := by
    intro u hu
    have htime : a + u ∈ Icc a d := ⟨by linarith only [hu.1], by linarith only [hu.2, hτ.2]⟩
    obtain ⟨E, hE, hd⟩ := hW (a + u) htime
    have hs : HasDerivAt (fun v : ℝ => a + v) 1 u := by
      have hadd := (hasDerivAt_const u a).add (hasDerivAt_id u)
      simp only [Pi.add_def, id_eq, zero_add] at hadd
      exact hadd
    have hWd := hd.scomp u hs
    have hRd := (P.hasDerivAt_shiftedRetardedTransfer hb ρ θp θc s (a + u)).scomp u hs
    simp only [one_smul, Function.comp_def] at hWd hRd
    refine ⟨E, hE, ?_⟩
    have hh := hWd.sub hRd
    convert hh using 1 <;> dsimp only [Z, c, R] <;> ring
  have hh := norm_linear_forced_residual_le hc0 hε (sub_nonneg.mpr hτ.1) Z hZE
  have hZ0 : Z 0 = W a - R a := by dsimp only [Z]; rw [add_zero]
  have hZτ : Z (τ - a) = W τ - R τ := by
    dsimp only [Z]
    rw [show a + (τ - a) = τ by ring]
  rw [hZ0, hZτ, hc] at hh
  exact hh

end CircularMaterialTransferProfile
end Euler2D

end
