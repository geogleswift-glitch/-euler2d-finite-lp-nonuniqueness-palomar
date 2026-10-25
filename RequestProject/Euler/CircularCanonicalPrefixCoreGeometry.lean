module

public import RequestProject.Euler.CircularPrefixNormalizedDomain
public import RequestProject.Euler.CircularAncestorTimeRescaling
public import RequestProject.Euler.CircularFiniteInnerInteractionRow

/-! Actual canonical quarter geometry places every active interface
inside each ancestor's rigid reference core at sufficiently small rho. -/

@[expose] public section

set_option maxHeartbeats 6000000

noncomputable section

open Complex Set Metric
open scoped NNReal

namespace Euler2D

theorem canonicalQuarterPhase_target_radius_upper {γ : ℝ≥0} {ι : Type*}
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {Z : ι → LittleContourSpace γ} (hZ : IsQuarterPhaseLittleContourFamily Z₀ r Z)
    (i : ι) (θ : ℝ) :
    ‖LittleContourSpace.lift γ (Z i) θ‖ ≤ (5 / 4 : ℝ) * r i := by
  obtain ⟨β, hβ⟩ := hZ
  have hd := (contourC1_norm_sub_ref_le (contourParameterShiftC1 (β i) (Z i).val)
    (Z₀ i) (href i) (θ - β i)).trans (hβ i).le
  have hdif : ‖LittleContourSpace.lift γ (Z i) θ - refCircle (r i) (θ - β i)‖ ≤ r i / 4 := by
    simpa only [lift_contourParameterShiftC1, sub_add_cancel] using hd
  have hn := norm_sub_norm_le (LittleContourSpace.lift γ (Z i) θ) (refCircle (r i) (θ - β i))
  rw [norm_refCircle_actual, abs_of_pos (hr i)] at hn
  linarith

theorem canonicalPrefix_cell_in_ancestor_core {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρcore : (5 / 4 : ℝ) * ρ ≤ cellA) {k : ℕ}
    (Z : FiniteCircularIndex k → LittleContourSpace γ)
    (hZ : IsQuarterPhaseLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) Z)
    (j : Fin (k + 1)) (i : Fin 2) (θ : ℝ) (l : Fin (j : ℕ)) :
    ‖LittleContourSpace.lift γ (Z (j, i)) θ‖ ≤ cellA * radScale R ρ l := by
  have hn := canonicalQuarterPhase_target_radius_upper (finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
    (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hZ (j, i) θ
  have hd : circularContourRadii i ≤ 1 := (circularContourRadii_bounds i).2.2
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hrl : 0 < radScale R ρ l := radScale_pos hR hρ l
  have hrad : radScale R ρ j ≤ radScale R ρ l * ρ := by
    have hp : ρ ^ ((j : ℕ) - l) ≤ ρ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (show 1 ≤ (j : ℕ) - l by omega)
    have hratio := (div_le_iff₀ hrl).mp ((radScale_ratio_eq_pow hR.ne' hρ.ne' l.isLt.le).trans_le hp)
    exact hratio.trans_eq (mul_comm _ _)
  calc
    _ ≤ (5 / 4 : ℝ) * radScale R ρ j := by
      have hh := mul_le_mul_of_nonneg_left hd hrj.le
      dsimp only [finiteCircularInterfaceRadius] at hn
      nlinarith only [hn, hh]
    _ ≤ (5 / 4 : ℝ) * (radScale R ρ l * ρ) := mul_le_mul_of_nonneg_left hrad (by norm_num)
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hρcore hrl.le]

end Euler2D

end
