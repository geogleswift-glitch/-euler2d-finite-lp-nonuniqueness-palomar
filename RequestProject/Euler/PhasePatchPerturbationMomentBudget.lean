module

public import RequestProject.Euler.PhaseOuterContourForcing
public import RequestProject.Euler.LabelInteractions

/-! Support, L1 and fourth absolute moment of the genuine phase patch
minus its circular reference. Every bound is linear in that source's
own contour deviation. -/

@[expose] public section

set_option maxHeartbeats 2400000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem phaseFiniteContourPatchPerturbation_moment_budget
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z Z₀ : ι → ContourC1Space γ) (d β : ι → ℝ)
    {rl B q : ℝ} (hrl : 0 < rl) (hB : 0 ≤ B) (hq0 : 0 ≤ q)
    (hd : ∀ i, 0 < d i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (d i * rl))
    (hsmall : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ (d i * rl) / 4)
    (hq : ∀ i, ‖contourParameterShiftC1 (β i) (Z i) - Z₀ i‖ ≤ rl * q)
    (hmax : ∀ i, (5 / 4 : ℝ) * d i ≤ B) :
    let w := phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl)
    Integrable w ∧
      (∀ x, B * rl < ‖x‖ → w x = 0) ∧
      (∫ x : ℂ, |w x|) ≤ (4 * Real.pi * ∑ i, |g i| * d i) * rl ^ 2 * q ∧
      (∫ x : ℂ, ‖x‖ ^ 4 * |w x|) ≤
        (4 * Real.pi * ∑ i, |g i| * d i) * B ^ 4 * rl ^ 6 * q := by
  classical
  dsimp only
  let w := phaseFiniteContourPatchPerturbation g Z (fun i => d i * rl)
  let Cmass := 4 * Real.pi * ∑ i, |g i| * d i
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
        nlinarith only [hm, hsm, hx])]
    exact mul_zero _
  have hmass : (∫ x : ℂ, |w x|) ≤ Cmass * rl ^ 2 * q := by
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
        dsimp only [Cmass]
        ring
  refine ⟨hi, hsupp, hmass, ?_⟩
  calc
    _ ≤ (B * rl) ^ 4 * (∫ x : ℂ, |w x|) := fourth_le_mass hi hsupp
    _ ≤ (B * rl) ^ 4 * (Cmass * rl ^ 2 * q) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by dsimp only [Cmass]; ring

end Euler2D

end
