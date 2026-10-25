module

public import RequestProject.Euler.ContourCircularNormalResponse

/-! The tangential component of the true self and cross first variations.
Together with the normal component this determines the full mode image. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff BigOperators ComplexConjugate

namespace Euler2D

local instance (priority := 2000) tangentialResponseC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) tangentialResponseC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem circularTangentialResponse_self {r : ℝ} (hr : 0 < r) (N : ℕ) (η τ : ℂ) :
    (circularContourModeVariation r r ((N + 3 : ℕ) : ℤ)
        (circularNormalModePlus r η τ) (circularNormalModePlus r η τ) +
      circularContourModeVariation r r (-((N + 1 : ℕ) : ℤ))
        (circularNormalModeMinus r η τ) (circularNormalModeMinus r η τ)).im = 0 := by
  rw [circularContourModeVariation_self_positive hr (N + 3) (by omega),
    circularContourModeVariation_self_negative hr (N + 1) (by omega), add_zero]
  norm_num [circularNormalModePlus, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  ring

theorem circularTangentialResponse_inside {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s < r)
    (N : ℕ) (ηi τi ηj τj : ℂ) :
    (circularContourModeVariation r s ((N + 3 : ℕ) : ℤ)
        (circularNormalModePlus r ηi τi) (circularNormalModePlus s ηj τj) +
      circularContourModeVariation r s (-((N + 1 : ℕ) : ℤ))
        (circularNormalModeMinus r ηi τi) (circularNormalModeMinus s ηj τj)).im =
      Real.pi * (r * (s / r) ^ 2 * ηi.re - s * (s / r) ^ (N + 3) * ηj.re) := by
  rw [circularContourModeVariation_inside_positive hr hs hsr (N + 1),
    circularContourModeVariation_inside_negative hr hs hsr N]
  simp_rw [← Complex.ofReal_pow]
  norm_num [circularNormalModePlus, circularNormalModeMinus,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  simp only [← Complex.ofReal_div, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem circularTangentialResponse_outside {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hrs : r < s)
    (N : ℕ) (ηi τi ηj τj : ℂ) :
    (circularContourModeVariation r s ((N + 3 : ℕ) : ℤ)
        (circularNormalModePlus r ηi τi) (circularNormalModePlus s ηj τj) +
      circularContourModeVariation r s (-((N + 1 : ℕ) : ℤ))
        (circularNormalModeMinus r ηi τi) (circularNormalModeMinus s ηj τj)).im =
      Real.pi * (-r * ηi.re + s * (r / s) ^ (N + 1) * ηj.re) := by
  rw [circularContourModeVariation_outside_positive hr hs hrs (N + 1),
    circularContourModeVariation_outside_negative hr hs hrs N]
  simp_rw [← Complex.ofReal_pow]
  norm_num [circularNormalModePlus, circularNormalModeMinus,
    Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]
  simp only [← Complex.ofReal_div, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_im]
  ring

set_option maxHeartbeats 800000 in
theorem circularBoundaryDerivative_tangential_response {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (N : ℕ) (η τ : Fin 2 → ℂ) (i : Fin 2) :
    (contourC1BoundaryDerivative circularContourStrengths
      (fun j => circularReferenceContourC1 hγ hγ1 (circularContourRadii j)) i 0
        (circularNormalModeC1 hγ hγ1 N η τ)).im =
      (![ -3 * cellA / 4 * (η 0).re + 3 / 4 * cellA ^ (N + 1) * (η 1).re,
          5 / 4 * cellA ^ (N + 4) * (η 0).re - 3 / 4 * (η 1).re] : Fin 2 → ℝ) i := by
  have hr (j : Fin 2) : 0 < circularContourRadii j := by
    fin_cases j <;> simp [circularContourRadii, cellA_pos]
  have hinj : Function.Injective circularContourRadii := by
    intro j k h
    fin_cases j <;> fin_cases k <;>
      simp_all [circularContourRadii, cellA_lt_one.ne, cellA_lt_one.ne.symm]
  rw [circularNormalModeC1_eq_add, map_add,
    circularBoundaryDerivative_reference_mode hγ hγ1 circularContourRadii hr hinj,
    circularBoundaryDerivative_reference_mode hγ hγ1 circularContourRadii hr hinj,
    ← smul_add, ← Finset.sum_add_distrib]
  simp_rw [← smul_add]
  change Complex.imCLM ((-1 / (2 * Real.pi) : ℝ) • ∑ j,
      circularContourStrengths j •
        (circularContourModeVariation (circularContourRadii i) (circularContourRadii j) ((N + 3 : ℕ) : ℤ)
          (circularNormalModePlus (circularContourRadii i) (η i) (τ i))
          (circularNormalModePlus (circularContourRadii j) (η j) (τ j)) +
        circularContourModeVariation (circularContourRadii i) (circularContourRadii j) (-((N + 1 : ℕ) : ℤ))
          (circularNormalModeMinus (circularContourRadii i) (η i) (τ i))
          (circularNormalModeMinus (circularContourRadii j) (η j) (τ j)))) = _
  rw [map_smul, map_sum]
  simp only [map_smul, Complex.imCLM_apply, smul_eq_mul, Fin.sum_univ_two]
  fin_cases i
  · have hself := circularTangentialResponse_self cellA_pos N (η 0) (τ 0)
    have hcross := circularTangentialResponse_outside cellA_pos (by norm_num) cellA_lt_one N
      (η 0) (τ 0) (η 1) (τ 1)
    norm_num [Complex.add_im] at hself hcross
    norm_num [circularContourRadii, circularContourStrengths]
    rw [hself, hcross]
    field_simp [Real.pi_ne_zero]
    <;> ring
  · have hself := circularTangentialResponse_self (by norm_num : (0 : ℝ) < 1) N (η 1) (τ 1)
    have hcross := circularTangentialResponse_inside (by norm_num) cellA_pos cellA_lt_one N
      (η 1) (τ 1) (η 0) (τ 0)
    norm_num [Complex.add_im] at hself hcross
    norm_num [circularContourRadii, circularContourStrengths]
    rw [hcross, hself]
    simp only [div_one, one_mul, cellA_sq]
    simp only [pow_succ]
    field_simp [Real.pi_ne_zero]
    <;> ring

end Euler2D

end
