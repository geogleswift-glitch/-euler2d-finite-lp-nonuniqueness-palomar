module

public import RequestProject.Euler.CircularFourierOperatorBounds

/-! Absolutely summable operator-valued normal/tangential symbols
give actual bounded operators on the unchanged little contour space. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set
open scoped NNReal ContDiff ComplexConjugate

namespace Euler2D

local instance (priority := 2000) blockMultiplierLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) blockMultiplierLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) blockMultiplierFamily_tower (γ : ℝ≥0) :
    IsScalarTower ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_assoc a b Z := by
    funext i
    change (a * b) • Z i = a • (b • Z i)
    exact (smul_smul a b (Z i)).symm
local instance (priority := 2000) blockMultiplierFamily_smulComm (γ : ℝ≥0) :
    SMulCommClass ℝ ℝ (Fin 2 → LittleContourSpace γ) where
  smul_comm a b Z := by
    funext i
    change a • (b • Z i) = b • (a • Z i)
    rw [smul_smul, smul_smul, mul_comm a b]

theorem circularModeAmplitudeCoefficient_embedding {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N M : ℕ) (p : CircularFourierAmplitudes) :
    circularModeAmplitudeCoefficientCLM γ N (circularModeAmplitudeEmbeddingCLM hγ hγ1 M p) =
      if N = M then p else 0 := by
  rw [circularModeAmplitudeEmbeddingCLM_apply]
  by_cases hNM : N = M
  · subst M
    rw [if_pos rfl, circularModeAmplitudeCoefficientCLM_normalMode]
  · rw [if_neg hNM]
    have hpp : ((M + 3 : ℕ) : ℤ) ≠ ((N + 3 : ℕ) : ℤ) := by omega
    have hnp : -((M + 1 : ℕ) : ℤ) ≠ ((N + 3 : ℕ) : ℤ) := by omega
    have hpn : ((M + 3 : ℕ) : ℤ) ≠ -((N + 1 : ℕ) : ℤ) := by omega
    have hnn : -((M + 1 : ℕ) : ℤ) ≠ -((N + 1 : ℕ) : ℤ) := by omega
    have hp (i : Fin 2) : littleContourFourierCoefficient γ ((N + 3 : ℕ) : ℤ)
        (circularNormalModeLittle hγ hγ1 M p.1 p.2 i) = 0 := by
      rw [littleContourFourierCoefficient_circularNormalMode]
      simp only [if_neg hpp, if_neg hnp, add_zero]
    have hn (i : Fin 2) : littleContourFourierCoefficient γ (-((N + 1 : ℕ) : ℤ))
        (circularNormalModeLittle hγ hγ1 M p.1 p.2 i) = 0 := by
      rw [littleContourFourierCoefficient_circularNormalMode]
      simp only [if_neg hpn, if_neg hnn, add_zero]
    apply Prod.ext
    · funext i
      change littleContourModeNormalCoefficientCLM γ (circularContourRadii i) N
        (circularNormalModeLittle hγ hγ1 M p.1 p.2 i) = 0
      rw [littleContourModeNormalCoefficientCLM_apply, hp, hn]
      simp
    · funext i
      change littleContourModeTangentCoefficientCLM γ (circularContourRadii i) N
        (circularNormalModeLittle hγ hγ1 M p.1 p.2 i) = 0
      rw [littleContourModeTangentCoefficientCLM_apply, hp, hn]
      simp

def circularFourierBlockTermCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (A : CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  (circularModeAmplitudeEmbeddingCLM hγ hγ1 N).comp
    (A.comp (circularModeAmplitudeCoefficientCLM γ N))

theorem norm_circularFourierBlockTermCLM_le {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (N : ℕ) (A : CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes) :
    ‖circularFourierBlockTermCLM hγ hγ1 N A‖ ≤
      (circularFourierModeWeight γ N * ‖A‖) * (2 / cellA) := by
  have ha : 0 ≤ (2 / cellA : ℝ) := by have hp := cellA_pos; positivity
  apply (circularFourierBlockTermCLM hγ hγ1 N A).opNorm_le_bound
    (mul_nonneg (mul_nonneg (circularFourierModeWeight_nonneg γ N) (norm_nonneg A)) ha)
  intro H
  change ‖circularModeAmplitudeEmbeddingCLM hγ hγ1 N
    (A (circularModeAmplitudeCoefficientCLM γ N H))‖ ≤ _
  calc
    _ ≤ circularFourierModeWeight γ N * ‖A (circularModeAmplitudeCoefficientCLM γ N H)‖ :=
      norm_circularModeAmplitudeEmbedding_le hγ hγ1 N _
    _ ≤ circularFourierModeWeight γ N * (‖A‖ * ‖circularModeAmplitudeCoefficientCLM γ N H‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (circularFourierModeWeight_nonneg γ N)
    _ ≤ circularFourierModeWeight γ N * (‖A‖ * ((2 / cellA) * ‖H‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_circularModeAmplitudeCoefficient_le N H) (norm_nonneg A))
        (circularFourierModeWeight_nonneg γ N)
    _ = _ := by ring

theorem summable_circularFourierBlockTermCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖)) :
    Summable (fun N => circularFourierBlockTermCLM hγ hγ1 N (A N)) :=
  (hA.mul_right (2 / cellA)).of_norm_bounded
    (fun N => norm_circularFourierBlockTermCLM_le hγ hγ1 N (A N))

def circularFourierBlockMultiplierCLM {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes) :
    (Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ) :=
  ∑' N : ℕ, circularFourierBlockTermCLM hγ hγ1 N (A N)

theorem norm_circularFourierBlockMultiplierCLM_le {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖)) :
    ‖circularFourierBlockMultiplierCLM hγ hγ1 A‖ ≤
      (∑' N : ℕ, circularFourierModeWeight γ N * ‖A N‖) * (2 / cellA) := by
  have h := tsum_of_norm_bounded (hA.mul_right (2 / cellA)).hasSum
    (fun N => norm_circularFourierBlockTermCLM_le hγ hγ1 N (A N))
  simpa only [tsum_mul_right, circularFourierBlockMultiplierCLM] using h

theorem circularModeAmplitudeCoefficient_multiplier {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    {A : ℕ → CircularFourierAmplitudes →L[ℝ] CircularFourierAmplitudes}
    (hA : Summable (fun N => circularFourierModeWeight γ N * ‖A N‖))
    (H : Fin 2 → LittleContourSpace γ) (N : ℕ) :
    circularModeAmplitudeCoefficientCLM γ N (circularFourierBlockMultiplierCLM hγ hγ1 A H) =
      A N (circularModeAmplitudeCoefficientCLM γ N H) := by
  have hs := summable_circularFourierBlockTermCLM hγ hγ1 hA
  let ev : ((Fin 2 → LittleContourSpace γ) →L[ℝ] (Fin 2 → LittleContourSpace γ)) →L[ℝ]
      (Fin 2 → LittleContourSpace γ) := ContinuousLinearMap.apply ℝ _ H
  have hv : Summable (fun M => circularFourierBlockTermCLM hγ hγ1 M (A M) H) :=
    (ev.hasSum hs.hasSum).summable
  change circularModeAmplitudeCoefficientCLM γ N
    (ev (∑' M, circularFourierBlockTermCLM hγ hγ1 M (A M))) = _
  rw [← (ev.hasSum hs.hasSum).tsum_eq]
  change circularModeAmplitudeCoefficientCLM γ N
    (∑' M, circularFourierBlockTermCLM hγ hγ1 M (A M) H) = _
  rw [← ((circularModeAmplitudeCoefficientCLM γ N).hasSum hv.hasSum).tsum_eq]
  change (∑' M, circularModeAmplitudeCoefficientCLM γ N
    (circularModeAmplitudeEmbeddingCLM hγ hγ1 M (A M (circularModeAmplitudeCoefficientCLM γ M H)))) = _
  simp only [circularModeAmplitudeCoefficient_embedding]
  rw [tsum_eq_single N (fun M hMN => if_neg (Ne.symm hMN)), if_pos rfl]

end Euler2D

end
