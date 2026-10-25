module

public import RequestProject.Euler.CircularUncoupledAmplitudeFlow

/-! The true full amplitude exponential at twice the material period
is exponentially close to the identity at high angular frequency. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set NormedSpace Filter Topology
open scoped NNReal ContDiff

namespace Euler2D

def circularAmplitudeCrossGenerator (N : ℕ) :
    CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes :=
  circularAmplitudeGenerator N - circularUncoupledAmplitudeGenerator N

set_option maxHeartbeats 600000 in
theorem circularAmplitudeCrossGenerator_apply (N : ℕ) (p : CircularFourierAmplitudes) :
    circularAmplitudeCrossGenerator N p =
      (![(-I * (3 / 4 : ℂ) * (cellA : ℂ) ^ N) * p.1 1,
          (I * (5 / 4 : ℂ) * (cellA : ℂ) ^ (N + 4)) * p.1 0],
        ![((3 / 4 : ℂ) * (cellA : ℂ) ^ N) * p.1 1,
          ((5 / 4 : ℂ) * (cellA : ℂ) ^ (N + 4)) * p.1 0]) := by
  rw [circularAmplitudeCrossGenerator, ContinuousLinearMap.sub_apply,
    circularAmplitudeGenerator_apply, circularUncoupledAmplitudeGenerator_apply]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    norm_num [circularAngularNormalAmplitude, circularAngularTangentialAmplitude,
      circularMaterialTangentialAmplitude, circularDiagonalNormalFrequency,
      circularDiagonalTangentFrequency, circularDiagonalTangentForcing,
      circularContourAngularVelocities, Bmat, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail,
      dotProduct, Fin.sum_univ_two]
    <;> push_cast <;> ring <;> simp_all

theorem norm_circularAmplitudeCrossGenerator_le (N : ℕ) :
    ‖circularAmplitudeCrossGenerator N‖ ≤ (5 / 4 : ℝ) * cellA ^ N := by
  have ha0 := cellA_pos.le
  have hapow : cellA ^ (N + 4) ≤ cellA ^ N := by
    exact pow_le_pow_of_le_one ha0 cellA_lt_one.le (by omega)
  apply (circularAmplitudeCrossGenerator N).opNorm_le_bound (by positivity)
  intro p
  have hp (i : Fin 2) : ‖p.1 i‖ ≤ ‖p‖ :=
    (norm_le_pi_norm p.1 i).trans (le_max_left _ _)
  have ha (k : ℕ) : ‖(cellA : ℂ) ^ k‖ = cellA ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos cellA_pos]
  rw [circularAmplitudeCrossGenerator_apply]
  apply max_le <;> apply (pi_norm_le_iff_of_nonneg (by positivity :
    (0 : ℝ) ≤ (5 / 4 : ℝ) * cellA ^ N * ‖p‖)).mpr <;>
    intro i <;> fin_cases i
  · change ‖(-I * (3 / 4 : ℂ) * (cellA : ℂ) ^ N) * p.1 1‖ ≤ _
    norm_num [norm_mul, ha]
    calc
      _ ≤ (5 / 4 : ℝ) * cellA ^ N * ‖p.1 1‖ := by
        nlinarith [mul_nonneg (pow_nonneg ha0 N) (norm_nonneg (p.1 1))]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hp 1) (by positivity)
  · change ‖(I * (5 / 4 : ℂ) * (cellA : ℂ) ^ (N + 4)) * p.1 0‖ ≤ _
    norm_num [norm_mul, ha]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hapow (by norm_num : (0 : ℝ) ≤ 5 / 4)) (hp 0)
      (norm_nonneg (p.1 0)) (by positivity : (0 : ℝ) ≤ 5 / 4 * cellA ^ N)
  · change ‖((3 / 4 : ℂ) * (cellA : ℂ) ^ N) * p.1 1‖ ≤ _
    norm_num [norm_mul, ha]
    calc
      _ ≤ (5 / 4 : ℝ) * cellA ^ N * ‖p.1 1‖ := by
        nlinarith [mul_nonneg (pow_nonneg ha0 N) (norm_nonneg (p.1 1))]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hp 1) (by positivity)
  · change ‖((5 / 4 : ℂ) * (cellA : ℂ) ^ (N + 4)) * p.1 0‖ ≤ _
    norm_num [norm_mul, ha]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hapow (by norm_num : (0 : ℝ) ≤ 5 / 4)) (hp 0)
      (norm_nonneg (p.1 0)) (by positivity : (0 : ℝ) ≤ 5 / 4 * cellA ^ N)

theorem circularAmplitudeGenerator_eq_uncoupled_add_cross (N : ℕ) :
    circularAmplitudeGenerator N = circularUncoupledAmplitudeGenerator N +
      circularAmplitudeCrossGenerator N := by
  unfold circularAmplitudeCrossGenerator
  abel

theorem norm_circularAmplitude_doublePeriod_sub_id_le (N : ℕ)
    (hsmall : 9 * ((5 / 4 : ℝ) * cellA ^ N) * (2 * period) ≤ 1) :
    ‖exp ((2 * period) • circularAmplitudeGenerator N) -
      ContinuousLinearMap.id ℝ CircularFourierAmplitudes‖ ≤
        (135 * period) * cellA ^ N := by
  have hT : 0 ≤ 2 * period := by unfold period; positivity
  have hnorm := norm_circularAmplitudeCrossGenerator_le N
  have hs : (3 : ℝ) ^ 2 * ‖circularAmplitudeCrossGenerator N‖ * (2 * period) ≤ 1 := by
    have hle := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 9)) hT
    norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num]
    exact hle.trans hsmall
  have h := norm_banachExponential_perturbation_le_small
    (circularUncoupledAmplitudeGenerator N) (circularAmplitudeCrossGenerator N)
    (M := 3) (T := 2 * period) (by norm_num) hT
    (fun t _ => norm_exp_circularUncoupledAmplitudeGenerator_le N t)
    (fun t _ => norm_exp_circularUncoupledAmplitudeGenerator_le N (-t)) hs
  rw [← circularAmplitudeGenerator_eq_uncoupled_add_cross,
    exp_circularUncoupledAmplitudeGenerator_double_period] at h
  calc
    _ ≤ 2 * 3 ^ 3 * (2 * period) * ‖circularAmplitudeCrossGenerator N‖ := h
    _ ≤ 2 * 3 ^ 3 * (2 * period) * ((5 / 4 : ℝ) * cellA ^ N) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

theorem eventually_norm_circularAmplitude_doublePeriod_sub_id_le :
    ∀ᶠ N : ℕ in atTop,
      ‖exp ((2 * period) • circularAmplitudeGenerator N) -
        ContinuousLinearMap.id ℝ CircularFourierAmplitudes‖ ≤ (135 * period) * cellA ^ N := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one cellA_pos.le cellA_lt_one
  have hl : Tendsto (fun N : ℕ => 9 * ((5 / 4 : ℝ) * cellA ^ N) * (2 * period))
      atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.mul hp)).mul tendsto_const_nhds using 1 <;> ring
  have he := hl.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he] with N hN
  exact norm_circularAmplitude_doublePeriod_sub_id_le N hN.le

theorem exists_norm_circularAmplitude_doublePeriod_sub_id_geometric_bound :
    ∃ C > 0, ∀ N : ℕ,
      ‖exp ((2 * period) • circularAmplitudeGenerator N) -
        ContinuousLinearMap.id ℝ CircularFourierAmplitudes‖ ≤ C * cellA ^ N := by
  classical
  let R : ℕ → ℝ := fun N => ‖exp ((2 * period) • circularAmplitudeGenerator N) -
    ContinuousLinearMap.id ℝ CircularFourierAmplitudes‖
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_norm_circularAmplitude_doublePeriod_sub_id_le
  let S : ℝ := ∑ j ∈ Finset.range N₀, R j / cellA ^ j
  have hR (j : ℕ) : 0 ≤ R j := norm_nonneg _
  have hterm (j : ℕ) : 0 ≤ R j / cellA ^ j := div_nonneg (hR j) (pow_nonneg cellA_pos.le j)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => hterm j)
  have hp : 0 < period := by unfold period; positivity
  let C := 1 + 135 * period + S
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, fun N => ?_⟩
  change R N ≤ C * cellA ^ N
  by_cases hN : N < N₀
  · have ht : R N / cellA ^ N ≤ S :=
      Finset.single_le_sum (fun j _ => hterm j)
        (Finset.mem_range.mpr hN)
    calc
      _ ≤ S * cellA ^ N := (div_le_iff₀ (pow_pos cellA_pos N)).mp ht
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (pow_nonneg cellA_pos.le N)
  · calc
      _ ≤ (135 * period) * cellA ^ N := hN₀ N (le_of_not_gt hN)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (pow_nonneg cellA_pos.le N)

end Euler2D

end
