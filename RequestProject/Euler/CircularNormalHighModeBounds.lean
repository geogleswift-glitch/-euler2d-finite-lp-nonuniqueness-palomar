module

public import RequestProject.Euler.CircularFourierLinearFlow
public import RequestProject.Euler.CircularUncoupledAmplitudeFlow

/-! Uniform bounds for the genuine high-frequency normal evolution.
Explicit uniformly bounded spectral projectors integrate the actual generator. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

def circularHighD (N : ℕ) : ℝ := (N : ℝ) / 2 - 1
def circularHighDelta (N : ℕ) : ℝ := DeltaM (N + 2)
def circularHighB (N : ℕ) : ℝ := 3 / 4 * cellA ^ N
def circularHighC (N : ℕ) : ℝ := 5 / 4 * cellA ^ (N + 4)
def circularHighGap (N : ℕ) : ℝ := circularHighD N - 2 * circularHighDelta N
def circularHighMuOne (N : ℕ) : ℝ := -3 / 4 - circularHighD N + circularHighDelta N
def circularHighMuTwo (N : ℕ) : ℝ := -3 / 4 - circularHighDelta N

def circularHighQOne (N : ℕ) (η : CircularFourierVector) : CircularFourierVector :=
  ![((circularHighD N - circularHighDelta N : ℝ) : ℂ) * η 0 + (circularHighB N : ℂ) * η 1,
    -(circularHighC N : ℂ) * η 0 - (circularHighDelta N : ℂ) * η 1]

def circularHighQTwo (N : ℕ) (η : CircularFourierVector) : CircularFourierVector :=
  ![-(circularHighDelta N : ℂ) * η 0 - (circularHighB N : ℂ) * η 1,
    (circularHighC N : ℂ) * η 0 + ((circularHighD N - circularHighDelta N : ℝ) : ℂ) * η 1]

def circularHighProjectionOne (N : ℕ) (η : CircularFourierVector) : CircularFourierVector :=
  ((circularHighGap N : ℂ)⁻¹) • circularHighQOne N η

def circularHighProjectionTwo (N : ℕ) (η : CircularFourierVector) : CircularFourierVector :=
  ((circularHighGap N : ℂ)⁻¹) • circularHighQTwo N η

theorem circularHigh_parameters {N : ℕ} (hN : 8 ≤ N + 2) :
    2 ≤ circularHighD N ∧ 0 < circularHighDelta N ∧ circularHighDelta N < 1 / 4 ∧
      0 ≤ circularHighB N ∧ circularHighB N ≤ 3 / 4 ∧
      0 ≤ circularHighC N ∧ circularHighC N ≤ 5 / 4 ∧ 0 < circularHighGap N := by
  have hδ := DeltaM_bounds hN
  have hd : 2 ≤ circularHighD N := by
    have hNR : (6 : ℝ) ≤ N := by exact_mod_cast (show 6 ≤ N by omega)
    dsimp only [circularHighD]
    linarith
  have hbpow : cellA ^ N ≤ 1 := pow_le_one₀ cellA_pos.le cellA_lt_one.le
  have ha : 0 < cellA := cellA_pos
  have hcpow : cellA ^ (N + 4) ≤ 1 := pow_le_one₀ cellA_pos.le cellA_lt_one.le
  have hδ' : circularHighDelta N < 1 / 4 := hδ.2.1.trans_lt hδ.2.2
  refine ⟨hd, hδ.1, hδ', ?_, ?_, ?_, ?_, ?_⟩
  · unfold circularHighB; positivity
  · unfold circularHighB; nlinarith
  · unfold circularHighC; positivity
  · unfold circularHighC; nlinarith
  · unfold circularHighGap
    linarith

theorem circularHigh_relation {N : ℕ} (hN : 8 ≤ N + 2) :
    circularHighDelta N * (circularHighD N - circularHighDelta N) =
      circularHighB N * circularHighC N := by
  have h := DeltaM_relation hN
  have he : N + 2 + 2 = N + 4 := by omega
  simp only [Nat.add_sub_cancel, he] at h
  convert h using 1 <;>
    simp only [circularHighDelta, circularHighD, circularHighB, circularHighC, Nat.cast_add,
      Nat.cast_ofNat] <;> ring

theorem circularNormalGenerator_high_formula (N : ℕ) (η : CircularFourierVector) :
    circularNormalGenerator N η =
      ![I * (((-3 / 4 - circularHighD N : ℝ) : ℂ) * η 0 - (circularHighB N : ℂ) * η 1),
        I * ((circularHighC N : ℂ) * η 0 - 3 / 4 * η 1)] := by
  funext i
  fin_cases i <;>
    norm_num [circularNormalGenerator_apply, circularAngularNormalAmplitude, Bmat,
      circularHighD, circularHighB, circularHighC, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Nat.add_sub_cancel] <;>
    push_cast <;> ring

theorem circularNormalGenerator_complex_smul (N : ℕ) (z : ℂ) (η : CircularFourierVector) :
    circularNormalGenerator N (z • η) = z • circularNormalGenerator N η :=
  (circularNormalGeneratorComplex N).map_smul z η

theorem circularHighQOne_eigen {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    circularNormalGenerator N (circularHighQOne N η) =
      (I * (circularHighMuOne N : ℂ)) • circularHighQOne N η := by
  have hrel : (circularHighDelta N : ℂ) *
      ((circularHighD N : ℂ) - (circularHighDelta N : ℂ)) =
        (circularHighB N : ℂ) * (circularHighC N : ℂ) := by
    exact_mod_cast circularHigh_relation hN
  rw [circularNormalGenerator_high_formula]
  funext i
  fin_cases i <;>
    simp only [circularHighQOne, circularHighMuOne, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    push_cast
  · linear_combination -I * η 0 * hrel
  · linear_combination -I * η 1 * hrel

theorem circularHighQTwo_eigen {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    circularNormalGenerator N (circularHighQTwo N η) =
      (I * (circularHighMuTwo N : ℂ)) • circularHighQTwo N η := by
  have hrel : (circularHighDelta N : ℂ) *
      ((circularHighD N : ℂ) - (circularHighDelta N : ℂ)) =
        (circularHighB N : ℂ) * (circularHighC N : ℂ) := by
    exact_mod_cast circularHigh_relation hN
  rw [circularNormalGenerator_high_formula]
  funext i
  fin_cases i <;>
    simp only [circularHighQTwo, circularHighMuTwo, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    push_cast
  · linear_combination I * η 0 * hrel
  · linear_combination I * η 1 * hrel

theorem circularHighProjectionOne_eigen {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    circularNormalGenerator N (circularHighProjectionOne N η) =
      (I * (circularHighMuOne N : ℂ)) • circularHighProjectionOne N η := by
  rw [circularHighProjectionOne, circularNormalGenerator_complex_smul, circularHighQOne_eigen hN,
    smul_smul, smul_smul, mul_comm]

theorem circularHighProjectionTwo_eigen {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    circularNormalGenerator N (circularHighProjectionTwo N η) =
      (I * (circularHighMuTwo N : ℂ)) • circularHighProjectionTwo N η := by
  rw [circularHighProjectionTwo, circularNormalGenerator_complex_smul, circularHighQTwo_eigen hN,
    smul_smul, smul_smul, mul_comm]

theorem circularHighProjection_sum {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    circularHighProjectionOne N η + circularHighProjectionTwo N η = η := by
  have hg : (circularHighGap N : ℂ) ≠ 0 := by
    exact_mod_cast (circularHigh_parameters hN).2.2.2.2.2.2.2.ne'
  funext i
  fin_cases i <;>
    simp only [circularHighProjectionOne, circularHighProjectionTwo, circularHighQOne,
      circularHighQTwo, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
    field_simp [hg] <;>
    simp only [circularHighGap] <;> push_cast <;> ring

theorem norm_complex_pair_div_le {x y g M : ℝ} (hg : 0 < g) (hM : 0 ≤ M)
    (hxy : |x| + |y| ≤ 2 * g) {u v : ℂ} (hu : ‖u‖ ≤ M) (hv : ‖v‖ ≤ M) :
    ‖(g : ℂ)⁻¹ * ((x : ℂ) * u + (y : ℂ) * v)‖ ≤ 2 * M := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  calc
    _ ≤ g⁻¹ * (‖(x : ℂ) * u‖ + ‖(y : ℂ) * v‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.mpr hg.le)
    _ = g⁻¹ * (|x| * ‖u‖ + |y| * ‖v‖) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ g⁻¹ * ((|x| + |y|) * M) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hg.le)
      nlinarith [mul_le_mul_of_nonneg_left hu (abs_nonneg x),
        mul_le_mul_of_nonneg_left hv (abs_nonneg y)]
    _ ≤ g⁻¹ * ((2 * g) * M) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hxy hM) (inv_nonneg.mpr hg.le)
    _ = _ := by field_simp <;> ring

theorem norm_circularHighProjectionOne_le {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    ‖circularHighProjectionOne N η‖ ≤ 2 * ‖η‖ := by
  obtain ⟨hd, hδ0, hδ1, hb0, hb1, hc0, hc1, hg⟩ := circularHigh_parameters hN
  have hdδ : 0 ≤ circularHighD N - circularHighDelta N := by linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖η‖)).mpr
  intro i
  fin_cases i
  · have hxy : |circularHighD N - circularHighDelta N| + |circularHighB N| ≤
        2 * circularHighGap N := by
      rw [abs_of_nonneg hdδ, abs_of_nonneg hb0]
      dsimp only [circularHighGap]
      linarith
    exact norm_complex_pair_div_le hg (norm_nonneg η) hxy
      (norm_le_pi_norm η 0) (norm_le_pi_norm η 1)
  · have hxy : |-circularHighC N| + |-circularHighDelta N| ≤ 2 * circularHighGap N := by
      rw [abs_neg, abs_neg, abs_of_nonneg hc0, abs_of_pos hδ0]
      dsimp only [circularHighGap]
      linarith
    simpa only [circularHighProjectionOne, circularHighQOne, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_neg, sub_eq_add_neg,
      neg_mul] using norm_complex_pair_div_le hg (norm_nonneg η) hxy
        (norm_le_pi_norm η 0) (norm_le_pi_norm η 1)

theorem norm_circularHighProjectionTwo_le {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    ‖circularHighProjectionTwo N η‖ ≤ 2 * ‖η‖ := by
  obtain ⟨hd, hδ0, hδ1, hb0, hb1, hc0, hc1, hg⟩ := circularHigh_parameters hN
  have hdδ : 0 ≤ circularHighD N - circularHighDelta N := by linarith
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖η‖)).mpr
  intro i
  fin_cases i
  · have hxy : |-circularHighDelta N| + |-circularHighB N| ≤ 2 * circularHighGap N := by
      rw [abs_neg, abs_neg, abs_of_pos hδ0, abs_of_nonneg hb0]
      dsimp only [circularHighGap]
      linarith
    simpa only [circularHighProjectionTwo, circularHighQTwo, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Complex.ofReal_neg, sub_eq_add_neg, neg_mul] using
        norm_complex_pair_div_le hg (norm_nonneg η) hxy (norm_le_pi_norm η 0) (norm_le_pi_norm η 1)
  · have hxy : |circularHighC N| + |circularHighD N - circularHighDelta N| ≤
        2 * circularHighGap N := by
      rw [abs_of_nonneg hc0, abs_of_nonneg hdδ]
      dsimp only [circularHighGap]
      linarith
    exact norm_complex_pair_div_le hg (norm_nonneg η) hxy
      (norm_le_pi_norm η 0) (norm_le_pi_norm η 1)

def circularHighNormalCurve (N : ℕ) (η : CircularFourierVector) (t : ℝ) : CircularFourierVector :=
  circularUnitPhase (circularHighMuOne N) t • circularHighProjectionOne N η +
    circularUnitPhase (circularHighMuTwo N) t • circularHighProjectionTwo N η

theorem circularHighNormalCurve_hasDerivAt {N : ℕ} (hN : 8 ≤ N + 2)
    (η : CircularFourierVector) (t : ℝ) :
    HasDerivAt (circularHighNormalCurve N η)
      (circularNormalGenerator N (circularHighNormalCurve N η t)) t := by
  have h1 := (hasDerivAt_circularUnitPhase (circularHighMuOne N) t).smul_const
    (circularHighProjectionOne N η)
  have h2 := (hasDerivAt_circularUnitPhase (circularHighMuTwo N) t).smul_const
    (circularHighProjectionTwo N η)
  convert h1.add h2 using 1
  simp only [circularHighNormalCurve, map_add, circularNormalGenerator_complex_smul,
    circularHighProjectionOne_eigen hN, circularHighProjectionTwo_eigen hN, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem circularHighNormalCurve_zero {N : ℕ} (hN : 8 ≤ N + 2) (η : CircularFourierVector) :
    circularHighNormalCurve N η 0 = η := by
  simp only [circularHighNormalCurve, circularUnitPhase, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul]
  exact circularHighProjection_sum hN η

theorem circularNormalLinearFlow_high {N : ℕ} (hN : 8 ≤ N + 2)
    (η : CircularFourierVector) (t : ℝ) :
    circularNormalLinearFlow N η t = circularHighNormalCurve N η t := by
  have he := ODE_solution_unique_univ
    (v := fun _ z => circularNormalGenerator N z)
    (s := fun _ => (univ : Set CircularFourierVector))
    (fun _ => (circularNormalGenerator N).lipschitz.lipschitzOnWith)
    (fun t => ⟨circularNormalLinearFlow_hasDerivAt N η t, mem_univ _⟩)
    (fun t => ⟨circularHighNormalCurve_hasDerivAt hN η t, mem_univ _⟩)
    (t₀ := (0 : ℝ)) (by rw [circularNormalLinearFlow_zero, circularHighNormalCurve_zero hN])
  exact congrFun he t

theorem norm_circularNormalLinearFlow_high_le {N : ℕ} (hN : 8 ≤ N + 2)
    (η : CircularFourierVector) (t : ℝ) :
    ‖circularNormalLinearFlow N η t‖ ≤ 4 * ‖η‖ := by
  rw [circularNormalLinearFlow_high hN, circularHighNormalCurve]
  calc
    _ ≤ ‖circularUnitPhase (circularHighMuOne N) t • circularHighProjectionOne N η‖ +
        ‖circularUnitPhase (circularHighMuTwo N) t • circularHighProjectionTwo N η‖ := norm_add_le _ _
    _ = ‖circularHighProjectionOne N η‖ + ‖circularHighProjectionTwo N η‖ := by
      rw [norm_smul, norm_smul, norm_circularUnitPhase, norm_circularUnitPhase, one_mul, one_mul]
    _ ≤ _ := by linarith [norm_circularHighProjectionOne_le hN η, norm_circularHighProjectionTwo_le hN η]

end Euler2D

end
