module

public import RequestProject.Euler.CircularTangentialGrowth
public import RequestProject.Euler.CircularUnstableComplement

/-! On the genuine kernel of the growing fourth normal coordinate,
the actual normal flow decays and the full amplitude flow has only
linear growth, including the original tangential forcing. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open Complex Set
open scoped NNReal ContDiff

namespace Euler2D

def circularStableFourthEigenvalue : ℂ := -(sigma : ℂ) - 3 / 4 * I

theorem circularFourthNormal_ker_ellPlus {η : CircularFourierVector} (hη : ellPlus η = 0) :
    η = η 0 • (![1, -I * cellA] : CircularFourierVector) := by
  have hd : (2 * I * (cellA : ℂ)) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) cellA_ne
  have hdiv : η 1 / (2 * I * (cellA : ℂ)) = -(η 0 / 2) := by
    dsimp only [ellPlus] at hη
    linear_combination hη
  have h1 : η 1 = -I * (cellA : ℂ) * η 0 := by
    calc
      _ = -(η 0 / 2) * (2 * I * (cellA : ℂ)) := (div_eq_iff hd).mp hdiv
      _ = _ := by ring
  funext i
  fin_cases i
  · simp
  · change η 1 = η 0 * (-I * (cellA : ℂ))
    exact h1.trans (mul_comm _ _)

theorem circularNormalGenerator_fourth_ker_ellPlus {η : CircularFourierVector}
    (hη : ellPlus η = 0) :
    circularNormalGenerator 2 η = circularStableFourthEigenvalue • η := by
  rw [circularFourthNormal_ker_ellPlus hη, circularNormalGenerator_complex_smul]
  have he : circularNormalGenerator 2 (![1, -I * cellA] : CircularFourierVector) =
      circularStableFourthEigenvalue • (![1, -I * cellA] : CircularFourierVector) := iB4_vMinus
  rw [he, smul_smul, smul_smul, mul_comm (η 0) circularStableFourthEigenvalue]

theorem circularNormalLinearFlow_fourth_ker_ellPlus {η : CircularFourierVector}
    (hη : ellPlus η = 0) (t : ℝ) :
    circularNormalLinearFlow 2 η t = exp ((t : ℂ) * circularStableFourthEigenvalue) • η := by
  let β : ℝ → CircularFourierVector := fun s => exp ((s : ℂ) * circularStableFourthEigenvalue) • η
  have he (s : ℝ) : HasDerivAt (fun u : ℝ => exp ((u : ℂ) * circularStableFourthEigenvalue))
      (circularStableFourthEigenvalue * exp ((s : ℂ) * circularStableFourthEigenvalue)) s := by
    convert (((hasDerivAt_id s).ofReal_comp).mul_const circularStableFourthEigenvalue).cexp using 1 <;>
      simp only [id_eq, Complex.ofReal_one, one_mul] <;> ring
  have hb (s : ℝ) : HasDerivAt β (circularNormalGenerator 2 (β s)) s := by
    have h := (he s).smul_const η
    change HasDerivAt β ((circularStableFourthEigenvalue *
      exp ((s : ℂ) * circularStableFourthEigenvalue)) • η) s at h
    convert h using 1
    simp only [β, circularNormalGenerator_complex_smul,
      circularNormalGenerator_fourth_ker_ellPlus hη, smul_smul]
    congr 1
    ring
  have hβ0 : β 0 = η := by simp only [β, ofReal_zero, zero_mul, exp_zero, one_smul]
  have hsol := ODE_solution_unique_univ
    (v := fun _ z => circularNormalGenerator 2 z) (s := fun _ => (univ : Set CircularFourierVector))
    (fun _ => (circularNormalGenerator 2).lipschitz.lipschitzOnWith)
    (fun s => ⟨circularNormalLinearFlow_hasDerivAt 2 η s, mem_univ _⟩)
    (fun s => ⟨hb s, mem_univ _⟩)
    (t₀ := (0 : ℝ)) (by rw [circularNormalLinearFlow_zero, hβ0])
  exact congrFun hsol t

theorem norm_circularNormalLinearFlow_fourth_ker_ellPlus_le {η : CircularFourierVector}
    (hη : ellPlus η = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖circularNormalLinearFlow 2 η t‖ ≤ ‖η‖ := by
  rw [circularNormalLinearFlow_fourth_ker_ellPlus hη, norm_smul, Complex.norm_exp]
  have he : ((t : ℂ) * circularStableFourthEigenvalue).re = -t * sigma := by
    norm_num [circularStableFourthEigenvalue, Complex.mul_re]
  rw [he]
  have hb : Real.exp (-t * sigma) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sigma_pos])
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (norm_nonneg η)

theorem norm_circularAmplitudeLinearFlow_fourth_complement_le (p : CircularFourierAmplitudes)
    (hp : ellPlus p.1 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖circularAmplitudeLinearFlow 2 p t‖ ≤ (1 + 2 * t) * ‖p‖ := by
  have hn (s : ℝ) (hs : 0 ≤ s) : ‖(circularAmplitudeLinearFlow 2 p s).1‖ ≤ ‖p‖ := by
    rw [circularAmplitudeLinearFlow_normal 2 p hs]
    exact (norm_circularNormalLinearFlow_fourth_ker_ellPlus_le hp hs).trans (norm_fst_le p)
  have hτ := norm_circularAmplitudeLinearFlow_tangent_le_of_normal_bound 2 p ht
    (fun s hs => hn s hs.1)
  change max ‖(circularAmplitudeLinearFlow 2 p t).1‖
    ‖(circularAmplitudeLinearFlow 2 p t).2‖ ≤ _
  apply max_le
  · exact (hn t ht).trans (by nlinarith [norm_nonneg p])
  · have hp2 := norm_snd_le p
    nlinarith [norm_nonneg p]

end Euler2D

end
