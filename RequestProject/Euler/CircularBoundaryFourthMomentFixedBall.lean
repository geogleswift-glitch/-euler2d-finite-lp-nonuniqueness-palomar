module

public import RequestProject.Euler.CircularBoundaryFourthMoment
public import RequestProject.Euler.CircularCaptureBackwardMoment

/-! A real fixed-radius moment estimate, obtained from the original
degree-six boundary polynomial rather than an unspecified local chart. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal BigOperators BoundedContinuousFunction

namespace Euler2D

local instance (priority := 2000) fixedMomentC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) fixedMomentC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)
local instance (priority := 2000) fixedMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) fixedMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

lemma norm_pow_sub_pow_le_coarse_ball {E : Type*} [NormedCommRing E] [NormOneClass E]
    {a b : E} {B : ℝ} (hB : 1 ≤ B) (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ (n : ℝ) * B ^ n * ‖a - b‖ := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  induction n with
  | zero => simp
  | succ n ih =>
    have hbpow : ‖b ^ n‖ ≤ B ^ n :=
      (norm_pow_le b n).trans (pow_le_pow_left₀ (norm_nonneg b) hb n)
    have hstep : B ^ n ≤ B ^ (n + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hB0 n) hB
    calc
      _ = ‖(a ^ n - b ^ n) * a + b ^ n * (a - b)‖ := by
        congr 1
        rw [pow_succ, pow_succ]
        ring
      _ ≤ ‖(a ^ n - b ^ n) * a‖ + ‖b ^ n * (a - b)‖ := norm_add_le _ _
      _ ≤ ‖a ^ n - b ^ n‖ * ‖a‖ + ‖b ^ n‖ * ‖a - b‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ((n : ℝ) * B ^ n * ‖a - b‖) * B + B ^ (n + 1) * ‖a - b‖ :=
        add_le_add (mul_le_mul ih ha (norm_nonneg a) (by positivity))
          (mul_le_mul_of_nonneg_right (hbpow.trans hstep) (norm_nonneg _))
      _ = _ := by rw [Nat.cast_add, Nat.cast_one, pow_succ]; ring

theorem exists_contourFourthMoment_fixed_ball_bound (γ : ℝ≥0) {B : ℝ} (hB : 1 ≤ B) :
    ∃ C > 0, ∀ Z W : ContourC1Space γ, ‖Z‖ ≤ B → ‖W‖ ≤ B →
      ‖contourFourthMoment γ Z - contourFourthMoment γ W‖ ≤ C * ‖Z - W‖ := by
  let A := ContourC1Space.toBCF γ
  let D := contourDerivativeBCF γ
  let Q := contourRealPartBCF
  let J := contourComplexIntegralSymmetric
  let c : ℂ := -I / 5
  let Clinear := ‖A‖ + ‖D‖ + 1
  let V := Clinear * B
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hClinear : 1 ≤ Clinear := by dsimp only [Clinear]; linarith only [norm_nonneg A, norm_nonneg D]
  have hV : 1 ≤ V := by
    have hh := mul_nonneg (sub_nonneg.mpr hClinear) hB0
    dsimp only [V]
    nlinarith only [hh, hB]
  have hV0 : 0 ≤ V := zero_le_one.trans hV
  let Cprod := ‖Q‖ * (V ^ 5 * ‖D‖ + 5 * V ^ 6 * ‖A‖)
  have hCprod : 0 ≤ Cprod := by dsimp only [Cprod]; positivity
  let C := ‖c‖ * ‖J‖ * Cprod + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z W hZ hW
  have hAlinear : ‖A‖ ≤ Clinear := by dsimp only [Clinear]; linarith only [norm_nonneg D]
  have hDlinear : ‖D‖ ≤ Clinear := by dsimp only [Clinear]; linarith only [norm_nonneg A]
  have hbound (F : ContourC1Space γ →L[ℝ] (ContourCircle →ᵇ ℂ)) (hF : ‖F‖ ≤ Clinear)
      (Y : ContourC1Space γ) (hY : ‖Y‖ ≤ B) : ‖F Y‖ ≤ V :=
    (F.le_opNorm Y).trans ((mul_le_mul_of_nonneg_left hY (norm_nonneg F)).trans
      (mul_le_mul_of_nonneg_right hF hB0))
  have hAZ : ‖A Z‖ ≤ V := hbound A hAlinear Z hZ
  have hAW : ‖A W‖ ≤ V := hbound A hAlinear W hW
  have hDW : ‖D W‖ ≤ V := hbound D hDlinear W hW
  have hAdiff : ‖A Z - A W‖ ≤ ‖A‖ * ‖Z - W‖ := by rw [← map_sub]; exact A.le_opNorm _
  have hDdiff : ‖D Z - D W‖ ≤ ‖D‖ * ‖Z - W‖ := by rw [← map_sub]; exact D.le_opNorm _
  have hAZpow : ‖(A Z) ^ 5‖ ≤ V ^ 5 :=
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hAZ 5)
  have hPowDiff : ‖(A Z) ^ 5 - (A W) ^ 5‖ ≤ 5 * V ^ 5 * (‖A‖ * ‖Z - W‖) :=
    (norm_pow_sub_pow_le_coarse_ball hV hAZ hAW 5).trans
      (mul_le_mul_of_nonneg_left hAdiff (by positivity))
  have hQpow : ‖Q ((A Z) ^ 5)‖ ≤ ‖Q‖ * V ^ 5 :=
    (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hAZpow (norm_nonneg _))
  have hQdiff : ‖Q ((A Z) ^ 5 - (A W) ^ 5)‖ ≤
      ‖Q‖ * (5 * V ^ 5 * (‖A‖ * ‖Z - W‖)) :=
    (Q.le_opNorm _).trans (mul_le_mul_of_nonneg_left hPowDiff (norm_nonneg _))
  have hsplit : Q ((A Z) ^ 5) * D Z - Q ((A W) ^ 5) * D W =
      Q ((A Z) ^ 5) * (D Z - D W) + Q ((A Z) ^ 5 - (A W) ^ 5) * D W := by
    rw [map_sub]
    ring
  have hproduct : ‖Q ((A Z) ^ 5) * D Z - Q ((A W) ^ 5) * D W‖ ≤ Cprod * ‖Z - W‖ := by
    rw [hsplit]
    calc
      _ ≤ ‖Q ((A Z) ^ 5) * (D Z - D W)‖ + ‖Q ((A Z) ^ 5 - (A W) ^ 5) * D W‖ := norm_add_le _ _
      _ ≤ ‖Q ((A Z) ^ 5)‖ * ‖D Z - D W‖ + ‖Q ((A Z) ^ 5 - (A W) ^ 5)‖ * ‖D W‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖Q‖ * V ^ 5) * (‖D‖ * ‖Z - W‖) +
          (‖Q‖ * (5 * V ^ 5 * (‖A‖ * ‖Z - W‖))) * V :=
        add_le_add (mul_le_mul hQpow hDdiff (norm_nonneg _) (by positivity))
          (mul_le_mul hQdiff hDW (norm_nonneg _) (by positivity))
      _ = _ := by dsimp only [Cprod]; ring
  have hactual : ‖contourFourthMoment γ Z - contourFourthMoment γ W‖ ≤
      (‖c‖ * ‖J‖ * Cprod) * ‖Z - W‖ := by
    change ‖c * J (Q ((A Z) ^ 5) * D Z) - c * J (Q ((A W) ^ 5) * D W)‖ ≤ _
    rw [← mul_sub, ← map_sub, norm_mul]
    calc
      _ ≤ ‖c‖ * (‖J‖ * ‖Q ((A Z) ^ 5) * D Z - Q ((A W) ^ 5) * D W‖) :=
        mul_le_mul_of_nonneg_left (J.le_opNorm _) (norm_nonneg _)
      _ ≤ ‖c‖ * (‖J‖ * (Cprod * ‖Z - W‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hproduct (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  exact hactual.trans (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (norm_nonneg _))

theorem exists_circularBoundaryFourthMoment_fixed_ball_bound (γ : ℝ≥0) {B : ℝ} (hB : 1 ≤ B) :
    ∃ C > 0, ∀ Z W : Fin 2 → LittleContourSpace γ, ‖Z‖ ≤ B → ‖W‖ ≤ B →
      ‖circularBoundaryFourthMoment Z - circularBoundaryFourthMoment W‖ ≤ C * ‖Z - W‖ := by
  obtain ⟨Ccontour, hCcontour, hbound⟩ := exists_contourFourthMoment_fixed_ball_bound γ hB
  let Kstrength := ∑ i : Fin 2, ‖(circularContourStrengths i : ℂ)‖
  have hKstrength : 0 ≤ Kstrength := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let C := Kstrength * Ccontour + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z W hZ hW
  have hsplit : circularBoundaryFourthMoment Z - circularBoundaryFourthMoment W =
      ∑ i : Fin 2, (circularContourStrengths i : ℂ) *
        (contourFourthMoment γ (Z i).val - contourFourthMoment γ (W i).val) := by
    unfold circularBoundaryFourthMoment
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsingle (i : Fin 2) :
      ‖contourFourthMoment γ (Z i).val - contourFourthMoment γ (W i).val‖ ≤ Ccontour * ‖Z - W‖ := by
    have hiZ : ‖(Z i).val‖ ≤ B := (norm_le_pi_norm Z i).trans hZ
    have hiW : ‖(W i).val‖ ≤ B := (norm_le_pi_norm W i).trans hW
    have hd : ‖(Z i).val - (W i).val‖ ≤ ‖Z - W‖ := norm_le_pi_norm (Z - W) i
    exact (hbound (Z i).val (W i).val hiZ hiW).trans (mul_le_mul_of_nonneg_left hd hCcontour.le)
  calc
    _ = ‖∑ i : Fin 2, (circularContourStrengths i : ℂ) *
        (contourFourthMoment γ (Z i).val - contourFourthMoment γ (W i).val)‖ := congrArg norm hsplit
    _ ≤ ∑ i : Fin 2, ‖(circularContourStrengths i : ℂ)‖ *
        ‖contourFourthMoment γ (Z i).val - contourFourthMoment γ (W i).val‖ := by
      simpa only [norm_mul] using norm_sum_le (s := Finset.univ)
        (fun i : Fin 2 => (circularContourStrengths i : ℂ) *
          (contourFourthMoment γ (Z i).val - contourFourthMoment γ (W i).val))
    _ ≤ ∑ i : Fin 2, ‖(circularContourStrengths i : ℂ)‖ * (Ccontour * ‖Z - W‖) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hsingle i) (norm_nonneg _))
    _ = (Kstrength * Ccontour) * ‖Z - W‖ := by rw [← Finset.sum_mul]; dsimp only [Kstrength]; ring
    _ ≤ C * ‖Z - W‖ := mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (norm_nonneg _)

theorem exists_circularBoundaryFourthMoment_prescribed_reference_bound {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {r : ℝ} (hr : 0 ≤ r) :
    ∃ C > 0, ∀ (t : ℝ) (Y : Fin 2 → LittleContourSpace γ),
      ‖Y - littleCircularMaterialContours hγ hγ1 t‖ ≤ r →
      ‖circularBoundaryFourthMoment Y‖ ≤ C * ‖Y - littleCircularMaterialContours hγ hγ1 t‖ := by
  let B := ‖littleCircularReference hγ hγ1‖ + r + 1
  have hB : 1 ≤ B := by dsimp only [B]; linarith only [norm_nonneg (littleCircularReference hγ hγ1), hr]
  obtain ⟨C, hC, hbound⟩ := exists_circularBoundaryFourthMoment_fixed_ball_bound γ hB
  refine ⟨C, hC, ?_⟩
  intro t Y hY
  let Z := circularCoRotationCLM γ t Y
  have hnorm : ‖Z - littleCircularReference hγ hγ1‖ =
      ‖Y - littleCircularMaterialContours hγ hγ1 t‖ :=
    norm_circularCoRotationCLM_sub_reference hγ hγ1 t Y
  have hZ : ‖Z‖ ≤ B := by
    calc
      _ = ‖(Z - littleCircularReference hγ hγ1) + littleCircularReference hγ hγ1‖ := by congr 1; abel
      _ ≤ ‖Z - littleCircularReference hγ hγ1‖ + ‖littleCircularReference hγ hγ1‖ := norm_add_le _ _
      _ ≤ r + ‖littleCircularReference hγ hγ1‖ := add_le_add (by simpa only [hnorm] using hY) le_rfl
      _ ≤ B := by dsimp only [B]; linarith
  have hRef : ‖littleCircularReference hγ hγ1‖ ≤ B := by dsimp only [B]; linarith only [hr]
  have hmoment : circularBoundaryFourthMoment Z = circularBoundaryFourthMoment Y :=
    circularBoundaryFourthMoment_parameterShift _ Y
  have hh := hbound Z (littleCircularReference hγ hγ1) hZ hRef
  rw [circularBoundaryFourthMoment_reference hγ hγ1, sub_zero, hmoment, hnorm] at hh
  exact hh

end Euler2D

end
