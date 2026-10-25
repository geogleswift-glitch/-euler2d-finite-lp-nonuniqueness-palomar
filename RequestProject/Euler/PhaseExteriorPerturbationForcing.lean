module

public import RequestProject.Euler.PhaseOuterContourForcing
public import RequestProject.Euler.CircularPhysicalContourLittle
public import RequestProject.Euler.LabelInteractions

/-! A true material patch minus its circular reference gives an
exterior Little forcing linear in its actual contour displacement.
The sixth power of the physical scale ratio comes from the fourth
moment of this actual perturbation, not the absolute cell mass. -/

@[expose] public section

set_option maxHeartbeats 5000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem exists_phaseExteriorPerturbationContourLittle_ratio {γ η : ℝ≥0}
    (hη : (η : ℝ) ≤ 1) {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (d β : ι → ℝ)
    {rl rj B e L q : ℝ} (hrl : 0 < rl) (hrj : 0 < rj) (hB : 0 ≤ B)
    (he : 0 < e) (hq0 : 0 ≤ q) (hd : ∀ i, 0 < d i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (d i * rl))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ (d i * rl) / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ rl * q)
    (hmax : ∀ i, (5 / 4 : ℝ) * d i ≤ B)
    (hrot : ∀ i θ, ContourC1Space.lift γ (Z i) (θ + Real.pi / 2) =
      I * ContourC1Space.lift γ (Z i) θ)
    (hmass : (∫ x, phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl) x) = 0)
    (hsep : 8 * (B * rl) ≤ e * rj)
    (W : LittleContourSpace η)
    (hW : ∀ x, e * rj ≤ ‖ContourC1Space.toBCF η W.val x‖)
    (hL : ‖W‖ ≤ rj * L) :
    ∃ Q : LittleContourSpace η,
      (∀ θ, LittleContourSpace.lift η Q θ =
        velocityC (phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl))
          (LittleContourSpace.lift η W θ)) ∧
      ‖Q‖ / rj ≤ cauchyContourNormBudget 5 (η : ℝ) 1 e L *
        (4 * Real.pi * ∑ i, |g i| * d i) * B ^ 4 * (rl / rj) ^ 6 * q := by
  let w := phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl)
  let Cmass := 4 * Real.pi * ∑ i, |g i| * d i
  have hcm : 0 ≤ Cmass := mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hd i).le))
  have hi : Integrable w := integrable_phaseFiniteContourPatchPerturbation
    g Z Z₀ (fun i => d i * rl) (fun i => mul_pos (hd i) hrl) href β hsmall
  have hsupp : ∀ x, B * rl < ‖x‖ → w x = 0 := by
    intro x hx
    apply Finset.sum_eq_zero
    intro i _
    rw [phaseContourPatchPerturbation_zero_outside (Z i) (Z₀ i)
      (mul_pos (hd i) hrl) (href i) (β i) (hsmall i) (by
        have hm := mul_le_mul_of_nonneg_right (hmax i) hrl.le
        have hsm := hsmall i
        nlinarith)]
    exact mul_zero _
  have hmassL1 : (∫ x : ℂ, |w x|) ≤ Cmass * rl ^ 2 * q := by
    calc
      _ ≤ ∑ i, |g i| * (4 * Real.pi * (d i * rl) *
          ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖) :=
        integral_abs_phaseFiniteContourPatchPerturbation_le g Z Z₀ (fun i => d i * rl)
          (fun i => mul_pos (hd i) hrl) href β hsmall
      _ ≤ ∑ i, |g i| * (4 * Real.pi * (d i * rl) * (rl * q)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hq i) (by positivity [hd i])) (abs_nonneg _)
      _ = _ := by
        simp_rw [show ∀ i : ι, |g i| * (4 * Real.pi * (d i * rl) * (rl * q)) =
          (4 * Real.pi * rl ^ 2 * q) * (|g i| * d i) by intro i; ring]
        rw [← Finset.mul_sum]
        dsimp [Cmass]
        ring
  let M := (B * rl) ^ 4 * (Cmass * rl ^ 2 * q)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hm4 : (∫ x : ℂ, ‖x‖ ^ 4 * |w x|) ≤ M :=
    (fourth_le_mass hi hsupp).trans (mul_le_mul_of_nonneg_left hmassL1 (by positivity))
  have hsy : ∀ x, w (I * x) = w x :=
    phaseFiniteContourPatchPerturbation_fourfold g Z _ hrot
  obtain ⟨Q, hQ, hn⟩ := exists_clusterContourFieldC1 hη (mul_nonneg hB hrl.le)
    hi hsupp hmass hsy hm4 (mul_pos he hrj)
    (by nlinarith only [hsep, mul_nonneg hB hrl.le]) W.val hW
  have hmem := clusterContourFieldC1_mem_little hη (mul_nonneg hB hrl.le)
    hi hsupp hmass hsy hm4 (mul_pos he hrj) hsep W hW Q hQ
  have hn' := hn.trans (cauchyContourNormBudget_mono_length 5 (η : ℝ) hM
    (mul_pos he hrj) (norm_nonneg W) hL)
  rw [mul_comm e, cauchyContourNormBudget_physical_scale 5 (η : ℝ) hM hrj he L] at hn'
  refine ⟨⟨Q, hmem⟩, hQ, (div_le_div_of_nonneg_right hn' hrj.le).trans_eq ?_⟩
  dsimp [M, Cmass]
  field_simp [hrj.ne']
  <;> ring

end Euler2D

end

