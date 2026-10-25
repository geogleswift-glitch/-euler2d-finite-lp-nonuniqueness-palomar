module

public import RequestProject.Euler.CircularActualInnerMomentSplit
public import RequestProject.Euler.CircularAdjacentMomentClock

/-! The actual inner-cluster fourth moment on the child's clock is
the observed child moment with coefficient rho^6, plus a genuinely
higher-order contribution from all deeper labels, uniform in cutoff. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 7000

noncomputable section

open Complex Set MeasureTheory
open scoped NNReal ENNReal ComplexConjugate

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actual_adjacent_normalized_moment_close
    {s A₀ b R ρ Cb D η : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hhalf : ρ ^ 2 ≤ b / 2) (hCb : 0 ≤ Cb) (hD : 0 ≤ D)
    (N j : ℕ) (hjN : j + 1 ≤ N)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (t θp θc : ℝ) (M : ℂ)
    (hchild : ∀ z, Cb * radScale R ρ (j + 1) * (1 + D) < ‖z‖ →
      boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (j + 1)) t) z = 0)
    (hdeep : ∀ z, Cb * radScale R ρ (j + 1) * (1 + D) < ‖z‖ →
      P.finiteInnerClusterComplexSource s A₀ b R ρ N (j + 1) S t z = 0)
    (hclose : ‖momentN (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (j + 1)) t)) 4 -
      (ampScale A₀ b (j + 1) : ℂ) * (radScale R ρ (j + 1) : ℂ) ^ 6 *
        Complex.exp (-(4 * (θc : ℂ) * I)) * M‖ ≤
      ampScale A₀ b (j + 1) * radScale R ρ (j + 1) ^ 6 * η) :
    ‖(b : ℂ) * (((ampScale A₀ b j)⁻¹ : ℂ) * ((radScale R ρ j)⁻¹ : ℂ) ^ 6 *
        Complex.exp (4 * (θp : ℂ) * I) *
          momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N j S t) 4) -
      (ρ : ℂ) ^ 6 * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M‖ ≤
      (2 * finiteLabelMassBound * Cb ^ 4 / b) * ρ ^ 8 * (1 + D) ^ 4 + ρ ^ 6 * η := by
  let Ap := ampScale A₀ b j
  let rp := radScale R ρ j
  let Ac := ampScale A₀ b (j + 1)
  let rc := radScale R ρ (j + 1)
  let Rs := Cb * rc * (1 + D)
  let cR := b * Ap⁻¹ * rp⁻¹ ^ 6
  let c : ℂ := (cR : ℂ) * Complex.exp (4 * (θp : ℂ) * I)
  let Mt := momentN (P.finiteInnerClusterComplexSource s A₀ b R ρ N j S t) 4
  let Mc := momentN (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N (j + 1)) t)) 4
  let target : ℂ := (Ac : ℂ) * (rc : ℂ) ^ 6 * Complex.exp (-(4 * (θc : ℂ) * I)) * M
  have hAp : 0 < Ap := div_pos hA (pow_pos hb j)
  have hrp : 0 < rp := radScale_pos hR hρ j
  have hAc : 0 < Ac := div_pos hA (pow_pos hb (j + 1))
  have hrc : 0 < rc := radScale_pos hR hρ (j + 1)
  have hcR : 0 ≤ cR := by dsimp only [cR]; positivity
  have hRs : 0 ≤ Rs := by dsimp only [Rs]; positivity
  have hsmall : ρ ^ 2 < b := hhalf.trans_lt (by linarith only [hb])
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ ^ 2 / b := by
    have hh : ρ ^ 2 / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by linarith only [hhalf])
    linarith only [hh]
  have hscale : cR * (Ac * rc ^ 6) = ρ ^ 6 := by
    dsimp only [cR, Ap, rp, Ac, rc]
    rw [ampScale_succ_eq_div, radScale_succ_eq_mul]
    field_simp [show ampScale A₀ b j ≠ 0 from hAp.ne',
      show radScale R ρ j ≠ 0 from hrp.ne', hb.ne']
    <;> ring
  have hmass : finiteInnerClusterMassBudget A₀ b R ρ (j + 1) ≤
      2 * finiteLabelMassBound * Ac * rc ^ 2 * (ρ ^ 2 / b) := by
    unfold finiteInnerClusterMassBudget
    calc
      _ ≤ (finiteLabelMassBound * Ac * rc ^ 2 * (ρ ^ 2 / b)) / (1 / 2) :=
        div_le_div_of_nonneg_left (by positivity [finiteLabelMassBound_nonneg])
          (by norm_num : (0 : ℝ) < 1 / 2) hdenHalf
      _ = _ := by ring
  have hdeepError : cR * (Rs ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ (j + 1)) ≤
      (2 * finiteLabelMassBound * Cb ^ 4 / b) * ρ ^ 8 * (1 + D) ^ 4 := by
    calc
      _ ≤ cR * (Rs ^ 4 * (2 * finiteLabelMassBound * Ac * rc ^ 2 * (ρ ^ 2 / b))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (by positivity)) hcR
      _ = (cR * (Ac * rc ^ 6)) *
          ((2 * finiteLabelMassBound * Cb ^ 4 / b) * ρ ^ 2 * (1 + D) ^ 4) := by
        dsimp only [Rs]
        ring
      _ = _ := by rw [hscale]; ring
  have hmoment : ‖Mt - Mc‖ ≤ Rs ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ (j + 1) := by
    simpa only [Nat.add_sub_cancel] using
      (P.actual_parent_inner_moment_eq_child_add_deeper hs hA.le hb hR hRmax hρ hρ1 hsmall
        N (j + 1) (Nat.succ_pos j) hjN S t hRs hchild hdeep).2
  have hnormc : ‖c‖ = cR := by
    have hphase : ‖Complex.exp (4 * (θp : ℂ) * I)‖ = 1 := by
      rw [show 4 * (θp : ℂ) * I = ((4 * θp : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    simp only [c, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcR, hphase, mul_one]
  have hleading : c * target =
      (ρ : ℂ) ^ 6 * Complex.exp (4 * ((θp - θc : ℝ) : ℂ) * I) * M := by
    convert adjacent_normalized_fourth_moment_coefficient hA.ne' hb.ne' hR.ne' hρ.ne' j θp θc M using 1
    dsimp only [c, cR, target, Ap, rp, Ac, rc]
    push_cast
    ring
  have hleft : (b : ℂ) * (((ampScale A₀ b j)⁻¹ : ℂ) * ((radScale R ρ j)⁻¹ : ℂ) ^ 6 *
      Complex.exp (4 * (θp : ℂ) * I) * Mt) = c * Mt := by
    dsimp only [c, cR, Ap, rp]
    push_cast
    ring
  change ‖(b : ℂ) * (((ampScale A₀ b j)⁻¹ : ℂ) * ((radScale R ρ j)⁻¹ : ℂ) ^ 6 *
    Complex.exp (4 * (θp : ℂ) * I) * Mt) - _‖ ≤ _
  rw [hleft, ← hleading, show c * Mt - c * target = c * (Mt - Mc) + c * (Mc - target) by ring]
  calc
    _ ≤ ‖c * (Mt - Mc)‖ + ‖c * (Mc - target)‖ := norm_add_le _ _
    _ ≤ cR * (Rs ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ (j + 1)) +
        cR * (Ac * rc ^ 6 * η) := by
      rw [norm_mul c (Mt - Mc), norm_mul c (Mc - target), hnormc]
      exact add_le_add (mul_le_mul_of_nonneg_left hmoment hcR) (mul_le_mul_of_nonneg_left hclose hcR)
    _ = cR * (Rs ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ (j + 1)) + ρ ^ 6 * η := by
      calc
        _ = cR * (Rs ^ 4 * finiteInnerClusterMassBudget A₀ b R ρ (j + 1)) +
            (cR * (Ac * rc ^ 6)) * η := by ring
        _ = _ := by rw [hscale]
    _ ≤ _ := by linarith only [hdeepError]

end CircularMaterialTransferProfile
end Euler2D

end
