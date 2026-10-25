module

public import RequestProject.Euler.CircularFourierCoordinates
public import RequestProject.Euler.ContourGeometricFourierMultiplier

/-! Uniform extraction bounds and polynomial reconstruction bounds
for the genuine normal/tangential Fourier blocks on the original space. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) fourierBlockLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fourierBlockLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

theorem circularContourRadii_bounds (i : Fin 2) :
    0 < circularContourRadii i ∧ cellA ≤ circularContourRadii i ∧ circularContourRadii i ≤ 1 := by
  fin_cases i
  · change 0 < cellA ∧ cellA ≤ cellA ∧ cellA ≤ 1
    exact ⟨cellA_pos, le_rfl, cellA_lt_one.le⟩
  · change 0 < (1 : ℝ) ∧ cellA ≤ 1 ∧ (1 : ℝ) ≤ 1
    exact ⟨by norm_num, cellA_lt_one.le, le_rfl⟩

theorem norm_littleContourModeNormalCoefficient_le {γ : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (N : ℕ) (H : LittleContourSpace γ) :
    ‖littleContourModeNormalCoefficientCLM γ r N H‖ ≤ 2 / r * ‖H‖ := by
  rw [littleContourModeNormalCoefficientCLM_apply, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  calc
    _ ≤ (‖littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) H‖ +
        ‖conj (littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) H)‖) / r :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hr.le
    _ ≤ (‖H‖ + ‖H‖) / r := by
      rw [norm_conj]
      exact div_le_div_of_nonneg_right (add_le_add
        (norm_littleContourFourierCoefficient_le _ H)
        (norm_littleContourFourierCoefficient_le _ H)) hr.le
    _ = _ := by ring

theorem norm_littleContourModeTangentCoefficient_le {γ : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (N : ℕ) (H : LittleContourSpace γ) :
    ‖littleContourModeTangentCoefficientCLM γ r N H‖ ≤ 2 / r * ‖H‖ := by
  rw [littleContourModeTangentCoefficientCLM_apply, norm_mul, norm_div, norm_neg, norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  calc
    _ ≤ (1 / r) * (‖littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ) H‖ +
        ‖conj (littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ)) H)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (1 / r) * (‖H‖ + ‖H‖) := by
      rw [norm_conj]
      exact mul_le_mul_of_nonneg_left (add_le_add
        (norm_littleContourFourierCoefficient_le _ H)
        (norm_littleContourFourierCoefficient_le _ H)) (by positivity)
    _ = _ := by ring

theorem norm_circularModeAmplitudeCoefficient_le {γ : ℝ≥0}
    (N : ℕ) (H : Fin 2 → LittleContourSpace γ) :
    ‖circularModeAmplitudeCoefficientCLM γ N H‖ ≤ (2 / cellA) * ‖H‖ := by
  have hb : 0 ≤ (2 / cellA : ℝ) := by have ha := cellA_pos; positivity
  have hr (i : Fin 2) : (2 / circularContourRadii i : ℝ) ≤ 2 / cellA :=
    div_le_div_of_nonneg_left (by norm_num) cellA_pos (circularContourRadii_bounds i).2.1
  change max ‖circularModeNormalCoefficientCLM γ N H‖
    ‖circularModeTangentCoefficientCLM γ N H‖ ≤ _
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg H))).mpr
    intro i
    exact (norm_littleContourModeNormalCoefficient_le (circularContourRadii_bounds i).1 N (H i)).trans
      ((mul_le_mul_of_nonneg_right (hr i) (norm_nonneg (H i))).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm H i) hb))
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg H))).mpr
    intro i
    exact (norm_littleContourModeTangentCoefficient_le (circularContourRadii_bounds i).1 N (H i)).trans
      ((mul_le_mul_of_nonneg_right (hr i) (norm_nonneg (H i))).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm H i) hb))

theorem norm_circularModeAmplitudeCoefficientCLM_le (γ : ℝ≥0) (N : ℕ) :
    ‖circularModeAmplitudeCoefficientCLM γ N‖ ≤ 2 / cellA := by
  apply (circularModeAmplitudeCoefficientCLM γ N).opNorm_le_bound
    (by have ha := cellA_pos; positivity)
  exact norm_circularModeAmplitudeCoefficient_le N

def circularFourierModeWeight (γ : ℝ≥0) (N : ℕ) : ℝ :=
  contourFourierModeWeight γ ((N + 3 : ℕ) : ℤ) +
    contourFourierModeWeight γ (-((N + 1 : ℕ) : ℤ))

theorem circularFourierModeWeight_nonneg (γ : ℝ≥0) (N : ℕ) :
    0 ≤ circularFourierModeWeight γ N :=
  add_nonneg (contourFourierModeWeight_nonneg γ _) (contourFourierModeWeight_nonneg γ _)

def circularModeAmplitudeEmbeddingCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) :
    CircularFourierAmplitudes →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ContinuousLinearMap.pi fun i =>
    let E : CircularFourierAmplitudes →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
    let T : CircularFourierAmplitudes →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)
    let M := (ContinuousLinearMap.mul ℝ ℂ) ((circularContourRadii i : ℂ) / 2)
    let J := (ContinuousLinearMap.mul ℝ ℂ) I
    (littleContourFourierModeCLM hγ hγ1 ((N + 3 : ℕ) : ℤ)).comp (M.comp (E + J.comp T)) +
      (littleContourFourierModeCLM hγ hγ1 (-((N + 1 : ℕ) : ℤ))).comp
        (M.comp (Complex.conjCLE.toContinuousLinearMap.comp E +
          J.comp (Complex.conjCLE.toContinuousLinearMap.comp T)))

theorem circularModeAmplitudeEmbeddingCLM_apply {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (p : CircularFourierAmplitudes) :
    circularModeAmplitudeEmbeddingCLM hγ hγ1 N p =
      circularNormalModeLittle hγ hγ1 N p.1 p.2 := by
  funext i
  simp only [circularModeAmplitudeEmbeddingCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.mul_apply',
    littleContourFourierModeCLM_apply, circularNormalModeLittle, circularNormalModePlus,
    circularNormalModeMinus]
  rfl

theorem norm_circularNormalModePlus_le (i : Fin 2) (p : CircularFourierAmplitudes) :
    ‖circularNormalModePlus (circularContourRadii i) (p.1 i) (p.2 i)‖ ≤ ‖p‖ := by
  have hr := circularContourRadii_bounds i
  have hη : ‖p.1 i‖ ≤ ‖p‖ := (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
  have hτ : ‖p.2 i‖ ≤ ‖p‖ := (norm_le_pi_norm p.2 i).trans (norm_snd_le p)
  unfold circularNormalModePlus
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
  norm_num only [norm_ofNat]
  have hs : ‖p.1 i + I * p.2 i‖ ≤ 2 * ‖p‖ := by
    have h := norm_add_le (p.1 i) (I * p.2 i)
    rw [norm_mul, norm_I, one_mul] at h
    linarith
  calc
    _ ≤ (circularContourRadii i / 2) * (2 * ‖p‖) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hr.1.le (by norm_num))
    _ ≤ (1 / 2 : ℝ) * (2 * ‖p‖) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hr.2.2 (by norm_num)) (by positivity)
    _ = _ := by ring

theorem norm_circularNormalModeMinus_le (i : Fin 2) (p : CircularFourierAmplitudes) :
    ‖circularNormalModeMinus (circularContourRadii i) (p.1 i) (p.2 i)‖ ≤ ‖p‖ := by
  have hr := circularContourRadii_bounds i
  have hη : ‖p.1 i‖ ≤ ‖p‖ := (norm_le_pi_norm p.1 i).trans (norm_fst_le p)
  have hτ : ‖p.2 i‖ ≤ ‖p‖ := (norm_le_pi_norm p.2 i).trans (norm_snd_le p)
  unfold circularNormalModeMinus
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
  norm_num only [norm_ofNat]
  have hs : ‖conj (p.1 i) + I * conj (p.2 i)‖ ≤ 2 * ‖p‖ := by
    have h := norm_add_le (conj (p.1 i)) (I * conj (p.2 i))
    rw [norm_mul, norm_I, one_mul, norm_conj, norm_conj] at h
    linarith
  calc
    _ ≤ (circularContourRadii i / 2) * (2 * ‖p‖) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg hr.1.le (by norm_num))
    _ ≤ (1 / 2 : ℝ) * (2 * ‖p‖) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hr.2.2 (by norm_num)) (by positivity)
    _ = _ := by ring

theorem norm_circularModeAmplitudeEmbedding_le {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (p : CircularFourierAmplitudes) :
    ‖circularModeAmplitudeEmbeddingCLM hγ hγ1 N p‖ ≤ circularFourierModeWeight γ N * ‖p‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (circularFourierModeWeight_nonneg γ N) (norm_nonneg p))).mpr
  intro i
  rw [circularModeAmplitudeEmbeddingCLM_apply]
  change ‖littleContourFourierMode hγ hγ1 ((N + 3 : ℕ) : ℤ) _ +
    littleContourFourierMode hγ hγ1 (-((N + 1 : ℕ) : ℤ)) _‖ ≤ _
  calc
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ contourFourierModeWeight γ ((N + 3 : ℕ) : ℤ) *
          ‖circularNormalModePlus (circularContourRadii i) (p.1 i) (p.2 i)‖ +
        contourFourierModeWeight γ (-((N + 1 : ℕ) : ℤ)) *
          ‖circularNormalModeMinus (circularContourRadii i) (p.1 i) (p.2 i)‖ :=
      add_le_add (norm_littleContourFourierMode_le hγ hγ1 _ _) (norm_littleContourFourierMode_le hγ hγ1 _ _)
    _ ≤ contourFourierModeWeight γ ((N + 3 : ℕ) : ℤ) * ‖p‖ +
        contourFourierModeWeight γ (-((N + 1 : ℕ) : ℤ)) * ‖p‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_circularNormalModePlus_le i p)
        (contourFourierModeWeight_nonneg γ _))
        (mul_le_mul_of_nonneg_left (norm_circularNormalModeMinus_le i p)
          (contourFourierModeWeight_nonneg γ _))
    _ = _ := by unfold circularFourierModeWeight; ring

theorem norm_circularModeAmplitudeEmbeddingCLM_le {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) :
    ‖circularModeAmplitudeEmbeddingCLM hγ hγ1 N‖ ≤ circularFourierModeWeight γ N := by
  apply (circularModeAmplitudeEmbeddingCLM hγ hγ1 N).opNorm_le_bound
    (circularFourierModeWeight_nonneg γ N)
  exact norm_circularModeAmplitudeEmbedding_le hγ hγ1 N

theorem summable_circularFourierModeWeight_geometric (γ : ℝ≥0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun N : ℕ => circularFourierModeWeight γ N * r ^ N) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs0 := summable_geometric_of_norm_lt_one hr
  have hs1 : Summable (fun N : ℕ => (N : ℝ) * r ^ N) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hs2 : Summable (fun N : ℕ => (N : ℝ) ^ 2 * r ^ N) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  let q := Real.pi ^ (1 - (γ : ℝ))
  convert ((hs0.mul_left (6 + 10 * q)).add (hs1.mul_left (2 + 8 * q))).add
    (hs2.mul_left (2 * q)) using 1
  funext N
  simp only [circularFourierModeWeight, contourFourierModeWeight, Int.cast_natCast,
    Int.cast_neg, norm_neg, norm_natCast]
  push_cast
  dsimp only [q]
  ring

end Euler2D

end
