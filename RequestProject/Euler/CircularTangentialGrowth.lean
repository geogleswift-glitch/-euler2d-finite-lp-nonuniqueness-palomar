module

public import RequestProject.Euler.CircularNormalHighModeBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-! The actual tangential equation has only linear growth when the
normal amplitude is bounded. In particular every high full amplitude
flow has a uniform polynomial bound, including the genuine tangential forcing. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

theorem norm_rotating_forced_curve_le (freq : ℝ) {τ F : ℝ → ℂ}
    (hd : ∀ s, HasDerivAt τ (((freq : ℂ) * I) * τ s + F s) s)
    {t C : ℝ} (ht : 0 ≤ t) (hF : ∀ s ∈ Icc 0 t, ‖F s‖ ≤ C) :
    ‖τ t‖ ≤ ‖τ 0‖ + C * t := by
  let α : ℝ → ℂ := fun s => circularUnitPhase (-freq) s * τ s
  have hα (s : ℝ) : HasDerivAt α (circularUnitPhase (-freq) s * F s) s := by
    have h := (hasDerivAt_circularUnitPhase (-freq) s).mul (hd s)
    convert h using 1 <;> dsimp only [α] <;> push_cast <;> ring
  have hn (s : ℝ) : ‖α s‖ = ‖τ s‖ := by
    simp only [α, norm_mul, norm_circularUnitPhase, one_mul]
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc (0 : ℝ) t) => (hα s).hasDerivWithinAt)
    (C := C) (fun s hs => by
      rw [norm_mul, norm_circularUnitPhase, one_mul]
      exact hF s ⟨hs.1, hs.2.le⟩) t ⟨ht, le_rfl⟩
  rw [sub_zero] at hb
  calc
    _ = ‖α t‖ := (hn t).symm
    _ ≤ ‖α t - α 0‖ + ‖α 0‖ := by
      simpa only [sub_add_cancel] using norm_add_le (α t - α 0) (α 0)
    _ ≤ C * t + ‖τ 0‖ := add_le_add hb (hn 0).le
    _ = _ := by ring

theorem circularAngularTangentialAmplitude_eq_rotation_forcing (N : ℕ)
    (η τ : CircularFourierVector) (i : Fin 2) :
    circularAngularTangentialAmplitude N η τ i =
      ((circularDiagonalTangentFrequency N i : ℝ) : ℂ) * I * τ i +
        (circularTangentialCouplingMatrix N).mulVec η i := by
  fin_cases i <;>
    norm_num [circularAngularTangentialAmplitude, circularMaterialTangentialAmplitude,
      circularDiagonalTangentFrequency, circularContourAngularVelocities,
      circularTangentialCouplingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    push_cast <;> ring

theorem norm_circularTangentialCouplingMatrix_mulVec_le (N : ℕ) (η : CircularFourierVector) :
    ‖(circularTangentialCouplingMatrix N).mulVec η‖ ≤ 2 * ‖η‖ := by
  have ha0 := cellA_pos.le
  have hap (k : ℕ) : cellA ^ k ≤ 1 := pow_le_one₀ ha0 cellA_lt_one.le
  have ha (k : ℕ) : ‖(cellA : ℂ) ^ k‖ = cellA ^ k := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos cellA_pos]
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖η‖)).mpr
  intro i
  simp only [circularTangentialCouplingMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · change ‖(-5 / 4 : ℂ) * η 0 + ((3 / 4 : ℂ) * (cellA : ℂ) ^ N) * η 1‖ ≤ _
    calc
      _ ≤ ‖(-5 / 4 : ℂ) * η 0‖ + ‖((3 / 4 : ℂ) * (cellA : ℂ) ^ N) * η 1‖ := norm_add_le _ _
      _ = (5 / 4 : ℝ) * ‖η 0‖ + ((3 / 4 : ℝ) * cellA ^ N) * ‖η 1‖ := by norm_num [norm_mul, ha]
      _ ≤ (5 / 4 : ℝ) * ‖η‖ + (3 / 4 : ℝ) * ‖η‖ := by
        apply add_le_add (mul_le_mul_of_nonneg_left (norm_le_pi_norm η 0) (by norm_num))
        exact mul_le_mul
          (by nlinarith [hap N] : (3 / 4 : ℝ) * cellA ^ N ≤ 3 / 4)
          (norm_le_pi_norm η 1) (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  · change ‖((5 / 4 : ℂ) * (cellA : ℂ) ^ (N + 4)) * η 0 + (-3 / 4 : ℂ) * η 1‖ ≤ _
    calc
      _ ≤ ‖((5 / 4 : ℂ) * (cellA : ℂ) ^ (N + 4)) * η 0‖ + ‖(-3 / 4 : ℂ) * η 1‖ := norm_add_le _ _
      _ = ((5 / 4 : ℝ) * cellA ^ (N + 4)) * ‖η 0‖ + (3 / 4 : ℝ) * ‖η 1‖ := by norm_num [norm_mul, ha]
      _ ≤ (5 / 4 : ℝ) * ‖η‖ + (3 / 4 : ℝ) * ‖η‖ := by
        apply add_le_add _ (mul_le_mul_of_nonneg_left (norm_le_pi_norm η 1) (by norm_num))
        exact mul_le_mul
          (by nlinarith [hap (N + 4)] : (5 / 4 : ℝ) * cellA ^ (N + 4) ≤ 5 / 4)
          (norm_le_pi_norm η 0) (norm_nonneg _) (by norm_num)
      _ = _ := by ring

theorem norm_circularAmplitudeLinearFlow_tangent_le_of_normal_bound (N : ℕ)
    (p : CircularFourierAmplitudes) {t B : ℝ} (ht : 0 ≤ t)
    (hn : ∀ s ∈ Icc 0 t, ‖(circularAmplitudeLinearFlow N p s).1‖ ≤ B) :
    ‖(circularAmplitudeLinearFlow N p t).2‖ ≤ ‖p.2‖ + (2 * B) * t := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hn 0 ⟨le_rfl, ht⟩)
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p.2‖ + (2 * B) * t)).mpr
  intro i
  let τ : ℝ → ℂ := fun s => (circularAmplitudeLinearFlow N p s).2 i
  let F : ℝ → ℂ := fun s => (circularTangentialCouplingMatrix N).mulVec
    (circularAmplitudeLinearFlow N p s).1 i
  have hd (s : ℝ) : HasDerivAt τ
      ((((circularDiagonalTangentFrequency N i : ℝ) : ℂ) * I) * τ s + F s) s := by
    have h := (ContinuousLinearMap.proj i : CircularFourierVector →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt s
      (circularAmplitudeLinearFlow_tangential_hasDerivAt N p s)
    change HasDerivAt τ (circularAngularTangentialAmplitude N
      (circularAmplitudeLinearFlow N p s).1 (circularAmplitudeLinearFlow N p s).2 i) s at h
    rw [circularAngularTangentialAmplitude_eq_rotation_forcing] at h
    exact h
  have hF (s : ℝ) (hs : s ∈ Icc 0 t) : ‖F s‖ ≤ 2 * B :=
    (norm_le_pi_norm ((circularTangentialCouplingMatrix N).mulVec
      (circularAmplitudeLinearFlow N p s).1) i).trans
        ((norm_circularTangentialCouplingMatrix_mulVec_le N _).trans
          (mul_le_mul_of_nonneg_left (hn s hs) (by norm_num)))
  have h := norm_rotating_forced_curve_le (circularDiagonalTangentFrequency N i) hd ht hF
  have hτ0 : τ 0 = p.2 i := by simp only [τ, circularAmplitudeLinearFlow_zero]
  rw [hτ0] at h
  exact h.trans (add_le_add (norm_le_pi_norm p.2 i) le_rfl)

theorem norm_circularAmplitudeLinearFlow_high_le {N : ℕ} (hN : 8 ≤ N + 2)
    (p : CircularFourierAmplitudes) {t : ℝ} (ht : 0 ≤ t) :
    ‖circularAmplitudeLinearFlow N p t‖ ≤ (4 + 8 * t) * ‖p‖ := by
  have hn (s : ℝ) (hs : 0 ≤ s) :
      ‖(circularAmplitudeLinearFlow N p s).1‖ ≤ 4 * ‖p‖ := by
    rw [circularAmplitudeLinearFlow_normal N p hs]
    exact (norm_circularNormalLinearFlow_high_le hN p.1 s).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le p) (by norm_num))
  have hτ := norm_circularAmplitudeLinearFlow_tangent_le_of_normal_bound N p ht
    (fun s hs => hn s hs.1)
  change max ‖(circularAmplitudeLinearFlow N p t).1‖
    ‖(circularAmplitudeLinearFlow N p t).2‖ ≤ _
  apply max_le
  · exact (hn t ht).trans (by nlinarith [norm_nonneg p])
  · have hp := norm_snd_le p
    nlinarith [norm_nonneg p]

theorem norm_exp_circularAmplitudeGenerator_high_le {N : ℕ} (hN : 8 ≤ N + 2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • circularAmplitudeGenerator N)‖ ≤ 4 + 8 * t := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact fun p => norm_circularAmplitudeLinearFlow_high_le hN p ht

end Euler2D

end
