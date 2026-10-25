module

public import RequestProject.Euler.ContourHilbertEstimates

/-! # Explicit finite constants in the genuine Hilbert Hölder estimate -/

@[expose] public section

noncomputable section

open Real

namespace Euler2D

def hilbertSmallConstant (γ : ℝ) : ℝ :=
  4 * (3 : ℝ) ^ γ / γ + 4 * (2 : ℝ) ^ (γ - 1) / (1 - γ) + Real.log 3 + 8 / Real.pi

def hilbertLargeConstant (γ : ℝ) : ℝ :=
  (4 * Real.pi ^ γ / γ) / ((Real.pi / 4) ^ γ)

def hilbertHolderConstant (γ : ℝ) : ℝ := hilbertSmallConstant γ + hilbertLargeConstant γ

theorem hilbertSmallConstant_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    0 ≤ hilbertSmallConstant γ := by
  unfold hilbertSmallConstant
  have hl : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hd : 0 < 1 - γ := sub_pos.mpr hγ1
  positivity

theorem hilbertLargeConstant_nonneg {γ : ℝ} (hγ : 0 < γ) :
    0 ≤ hilbertLargeConstant γ := by unfold hilbertLargeConstant; positivity

theorem hilbertHolderConstant_nonneg {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) :
    0 ≤ hilbertHolderConstant γ :=
  add_nonneg (hilbertSmallConstant_nonneg hγ hγ1) (hilbertLargeConstant_nonneg hγ)

theorem hilbert_small_bound_normalize {γ h N : ℝ}
    (_hγ : 0 < γ) (hγ1 : γ < 1) (hh : 0 < h) (hsmall : h ≤ Real.pi / 4) (hN : 0 ≤ N) :
    N * (4 * (3 * h) ^ γ / γ) +
      ((4 * h * N) * ((2 * h) ^ (γ - 1) / (1 - γ)) + Real.log 3 * (N * h ^ γ)) +
      (8 * N / Real.pi) * h ≤ hilbertSmallConstant γ * N * h ^ γ := by
  have h3 : (3 * h) ^ γ = (3 : ℝ) ^ γ * h ^ γ := Real.mul_rpow (by norm_num) hh.le
  have h2 : (2 * h) ^ (γ - 1) = (2 : ℝ) ^ (γ - 1) * h ^ (γ - 1) :=
    Real.mul_rpow (by norm_num) hh.le
  have hp : h * h ^ (γ - 1) = h ^ γ := by
    rw [Real.rpow_sub_one hh.ne']
    field_simp [hh.ne']
  have hfar : (4 * h * N) * ((2 * h) ^ (γ - 1) / (1 - γ)) =
      (4 * (2 : ℝ) ^ (γ - 1) / (1 - γ)) * N * h ^ γ := by
    rw [h2]
    calc
      _ = (4 * (2 : ℝ) ^ (γ - 1) / (1 - γ)) * N * (h * h ^ (γ - 1)) := by ring
      _ = _ := by rw [hp]
  have hnear : N * (4 * (3 * h) ^ γ / γ) =
      (4 * (3 : ℝ) ^ γ / γ) * N * h ^ γ := by rw [h3]; ring
  have hh1 : h ≤ 1 := by linarith [Real.pi_lt_four]
  have hlow : h ≤ h ^ γ := Real.self_le_rpow_of_le_one hh.le hh1 hγ1.le
  rw [hnear, hfar]
  calc
    _ ≤ (4 * (3 : ℝ) ^ γ / γ) * N * h ^ γ +
        ((4 * (2 : ℝ) ^ (γ - 1) / (1 - γ)) * N * h ^ γ + Real.log 3 * (N * h ^ γ)) +
        (8 * N / Real.pi) * h ^ γ := by
      have hm : (8 * N / Real.pi) * h ≤ (8 * N / Real.pi) * h ^ γ :=
        mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 8 * N / Real.pi)
      exact add_le_add le_rfl hm
    _ = _ := by unfold hilbertSmallConstant; ring

theorem hilbert_large_bound_normalize {γ h N : ℝ}
    (hγ : 0 < γ) (hlarge : Real.pi / 4 ≤ h) (hN : 0 ≤ N) :
    4 * N * Real.pi ^ γ / γ ≤ hilbertLargeConstant γ * N * h ^ γ := by
  have hb : 0 < (Real.pi / 4) ^ γ := Real.rpow_pos_of_pos (by positivity) _
  have hpow : (Real.pi / 4) ^ γ ≤ h ^ γ :=
    Real.rpow_le_rpow (by positivity) hlarge hγ.le
  calc
    _ = N * (4 * Real.pi ^ γ / γ) := by ring
    _ = N * ((4 * Real.pi ^ γ / γ) / ((Real.pi / 4) ^ γ) * ((Real.pi / 4) ^ γ)) := by
      rw [div_mul_cancel₀ _ hb.ne']
    _ = hilbertLargeConstant γ * N * ((Real.pi / 4) ^ γ) := by
      unfold hilbertLargeConstant
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow
      (mul_nonneg (hilbertLargeConstant_nonneg hγ) hN)

end Euler2D

end
