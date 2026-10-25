module

public import RequestProject.Euler.CircularMaterialRetardedDifferentiability
public import RequestProject.Euler.GronwallForcingBound

/-! Compare a forced coordinate to the ORIGINAL profile's retarded
response on the same shifted clock. The unit phase is exact and
preserves the original nonzero response. Entrance error remains
explicit; it is not assumed to vanish or to be o(rho^6). -/

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

def shiftedRetardedTransfer (b ρ θp θc s : ℝ) (τ : ℝ) : ℂ :=
  Complex.exp ((((4 * (θp - θc) + 2 * b * s : ℝ) : ℂ)) * I) *
    retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
      ((ρ : ℂ) ^ 6 * Kstar) P.moment (s + τ)

theorem shiftedRetardedTransfer_norm (b ρ θp θc s τ : ℝ) :
    ‖P.shiftedRetardedTransfer b ρ θp θc s τ‖ =
      ‖retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (s + τ)‖ := by
  rw [shiftedRetardedTransfer, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem shiftedRetardedTransfer_ne_zero_iff (b ρ θp θc s τ : ℝ) :
    P.shiftedRetardedTransfer b ρ θp θc s τ ≠ 0 ↔
      retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (s + τ) ≠ 0 := by
  constructor
  · intro h hz
    apply h
    rw [shiftedRetardedTransfer, hz, mul_zero]
  · intro h
    exact mul_ne_zero (Complex.exp_ne_zero _) h

theorem hasDerivAt_shiftedRetardedTransfer {b : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (ρ θp θc s τ : ℝ) :
    HasDerivAt (P.shiftedRetardedTransfer b ρ θp θc s)
      (((b : ℂ) * lamStar) * P.shiftedRetardedTransfer b ρ θp θc s τ +
        (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
          Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) * P.moment (s + τ)) τ := by
  let u := Complex.exp ((((4 * (θp - θc) + 2 * b * s : ℝ) : ℂ)) * I)
  have hphase : u * Complex.exp (-(2 * I * b) * ((s + τ : ℝ) : ℂ)) =
      Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
        Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) := by
    dsimp only [u]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hshift : HasDerivAt (fun t : ℝ => s + t) 1 τ := by
    simpa only [zero_add] using (hasDerivAt_const τ s).add (hasDerivAt_id τ)
  have hraw := (P.hasDerivAt_retarded_transfer (ρ := ρ) hb (s + τ)).scomp τ hshift
  simp only [one_smul, Function.comp_def] at hraw
  have hh := hraw.const_mul u
  change HasDerivAt (P.shiftedRetardedTransfer b ρ θp θc s)
    (u * (((b : ℂ) * lamStar) *
      retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (s + τ) +
      ((ρ : ℂ) ^ 6 * Kstar) * Complex.exp (-(2 * I * b) * ((s + τ : ℝ) : ℂ)) *
        P.moment (s + τ))) τ at hh
  have hval : u * (((b : ℂ) * lamStar) *
      retardedSol ((b : ℂ) * lamStar) ((b : ℂ) * (sigma + 5 / 4 * I))
        ((ρ : ℂ) ^ 6 * Kstar) P.moment (s + τ) +
      ((ρ : ℂ) ^ 6 * Kstar) * Complex.exp (-(2 * I * b) * ((s + τ : ℝ) : ℂ)) *
        P.moment (s + τ)) =
      (((b : ℂ) * lamStar) * P.shiftedRetardedTransfer b ρ θp θc s τ +
        (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
          Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) * P.moment (s + τ)) := by
    calc
      _ = (((b : ℂ) * lamStar) * P.shiftedRetardedTransfer b ρ θp θc s τ +
          (ρ : ℂ) ^ 6 * Kstar * (u * Complex.exp (-(2 * I * b) * ((s + τ : ℝ) : ℂ))) *
            P.moment (s + τ)) := by dsimp only [shiftedRetardedTransfer, u]; ring
      _ = _ := by rw [hphase]; ring
  rw [hval] at hh
  exact hh

theorem dist_shiftedRetardedTransfer_le_of_forced_equation
    {b ρ θp θc s a d ε : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4)) (hε : 0 ≤ ε)
    (W : ℝ → ℂ)
    (hW : ∀ τ ∈ Icc a d, ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt W (((b : ℂ) * lamStar) * W τ +
        (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
          Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) * P.moment (s + τ) + E) τ) :
    ∀ τ ∈ Icc a d,
      ‖W τ - P.shiftedRetardedTransfer b ρ θp θc s τ‖ ≤
        (‖W a - P.shiftedRetardedTransfer b ρ θp θc s a‖ + ε * (τ - a)) *
          Real.exp (‖(b : ℂ) * lamStar‖ * (τ - a)) := by
  let c := (b : ℂ) * lamStar
  let F := fun τ : ℝ => (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) *
    Complex.exp (-((2 * b * τ : ℝ) : ℂ) * I) * P.moment (s + τ)
  let V := fun τ : ℝ => fun z : ℂ => c * z + F τ
  let R := P.shiftedRetardedTransfer b ρ θp θc s
  have hRc : Continuous R := by
    exact continuous_iff_continuousAt.mpr fun τ =>
      (P.hasDerivAt_shiftedRetardedTransfer hb ρ θp θc s τ).continuousAt
  have hWc : ContinuousOn W (Icc a d) := by
    intro τ hτ
    obtain ⟨E, _, hd⟩ := hW τ hτ
    exact hd.continuousAt.continuousWithinAt
  have hWd : ∀ τ ∈ Ico a d, HasDerivWithinAt W (deriv W τ) (Ici τ) τ := by
    intro τ hτ
    obtain ⟨E, _, hd⟩ := hW τ ⟨hτ.1, hτ.2.le⟩
    exact hd.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hWb : ∀ τ ∈ Ico a d, dist (deriv W τ) (V τ (W τ)) ≤ ε := by
    intro τ hτ
    obtain ⟨E, hE, hd⟩ := hW τ ⟨hτ.1, hτ.2.le⟩
    rw [hd.deriv, dist_eq_norm]
    simpa only [V, c, F, add_sub_cancel_left] using hE
  have hV : ∀ τ, LipschitzWith ‖c‖₊ (V τ) := by
    intro τ
    apply LipschitzWith.of_dist_le_mul
    intro z w
    change ‖c * z + F τ - (c * w + F τ)‖ ≤ ‖c‖ * ‖z - w‖
    rw [show c * z + F τ - (c * w + F τ) = c * (z - w) by ring, norm_mul]
  have hRd : ∀ τ ∈ Ico a d, HasDerivWithinAt R (V τ (R τ)) (Ici τ) τ :=
    fun τ _ => (P.hasDerivAt_shiftedRetardedTransfer hb ρ θp θc s τ).hasDerivWithinAt
  have hRb : ∀ τ ∈ Ico a d, dist (V τ (R τ)) (V τ (R τ)) ≤ 0 := by
    intro τ _
    simp only [dist_self, le_refl]
  have hinit : dist (W a) (R a) ≤ ‖W a - R a‖ := le_of_eq (dist_eq_norm _ _)
  intro τ hτ
  have hG := dist_le_of_approx_trajectories_ODE hV hWc hWd hWb hRc.continuousOn hRd hRb hinit τ hτ
  simp only [add_zero, coe_nnnorm, dist_eq_norm] at hG
  exact hG.trans (gronwallBound_le_add_mul_exp (norm_nonneg c) hε (sub_nonneg.mpr hτ.1))

end CircularMaterialTransferProfile
end Euler2D

end
