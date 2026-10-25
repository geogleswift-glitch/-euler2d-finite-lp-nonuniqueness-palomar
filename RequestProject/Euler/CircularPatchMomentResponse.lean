module

public import RequestProject.Euler.CircularGrowingMoment

/-! The fourth moment of the genuine two-interface vorticity label,
with the original strengths. The nonzero growing response includes
both actual enclosed domains and the full tangential perturbation. -/

@[expose] public section

noncomputable section

open Complex Set
open scoped NNReal ContDiff BigOperators

namespace Euler2D

local instance (priority := 2000) patchMomentLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) patchMomentLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)

def circularFamilyPatchFourthMoment {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (v : Fin 2 → LittleContourSpace γ) : ℂ :=
  ∑ i : Fin 2, (circularContourStrengths i : ℂ) * circularAreaChartFourthMoment hγ hγ1 i (v i)

def circularPatchGrowingResponse : ℂ :=
  (Real.pi : ℂ) * ((5 / 2 : ℂ) * (cellA : ℂ) ^ 6 - (3 / 2 : ℂ) * I * cellA)

theorem circularFamilyPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : circularFamilyPatchFourthMoment hγ hγ1 0 = 0 := by
  simp only [circularFamilyPatchFourthMoment, Pi.zero_apply,
    circularAreaChartFourthMoment_zero, mul_zero, Finset.sum_const_zero]

theorem differentiableAt_circularFamilyPatchFourthMoment_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    DifferentiableAt ℝ (circularFamilyPatchFourthMoment hγ hγ1) 0 := by
  have hd (i : Fin 2) : DifferentiableAt ℝ
      (fun v : Fin 2 → LittleContourSpace γ => circularAreaChartFourthMoment hγ hγ1 i (v i)) 0 := by
    let p : (Fin 2 → LittleContourSpace γ) →L[ℝ] LittleContourSpace γ := ContinuousLinearMap.proj i
    have hg : DifferentiableAt ℝ (circularAreaChartFourthMoment hγ hγ1 i)
        (p (0 : Fin 2 → LittleContourSpace γ)) := by
      simpa only [ContinuousLinearMap.map_zero] using
        differentiableAt_circularAreaChartFourthMoment_zero hγ hγ1 i
    exact hg.comp (0 : Fin 2 → LittleContourSpace γ) p.differentiableAt
  convert
    ((hd 0).const_mul (circularContourStrengths 0 : ℂ)).add
      ((hd 1).const_mul (circularContourStrengths 1 : ℂ)) using 1
  funext v
  simp only [circularFamilyPatchFourthMoment, Fin.sum_univ_two, Pi.add_apply]

theorem circularFamilyPatchFourthMoment_growing_hasDerivAt {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    HasDerivAt (fun s : ℝ => circularFamilyPatchFourthMoment hγ hγ1.le
      (s • circularGrowingVariation hγ hγ1 0)) circularPatchGrowingResponse 0 := by
  have h0 := (circularGrowingMoment_patch_hasDerivAt hγ hγ1 0).const_mul
    (circularContourStrengths 0 : ℂ)
  have h1 := (circularGrowingMoment_patch_hasDerivAt hγ hγ1 1).const_mul
    (circularContourStrengths 1 : ℂ)
  convert h0.add h1 using 1
  · funext s
    simp only [circularFamilyPatchFourthMoment, Fin.sum_univ_two, Pi.smul_apply, Pi.add_apply]
  · norm_num [circularContourStrengths, circularContourRadii, vPlus, circularPatchGrowingResponse]
    ring

theorem circularPatchGrowingResponse_re :
    circularPatchGrowingResponse.re = (5 / 2 : ℝ) * Real.pi * cellA ^ 6 := by
  simp only [circularPatchGrowingResponse, ← Complex.ofReal_pow]
  norm_num [Complex.mul_re, Complex.mul_im]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem circularPatchGrowingResponse_ne_zero : circularPatchGrowingResponse ≠ 0 := by
  intro hzero
  have hr := congrArg Complex.re hzero
  rw [circularPatchGrowingResponse_re, Complex.zero_re] at hr
  have hp : 0 < (5 / 2 : ℝ) * Real.pi * cellA ^ 6 := by have := cellA_pos; positivity
  exact hp.ne' hr

theorem fderiv_circularFamilyPatchFourthMoment_growing {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1.le) 0
      (circularGrowingVariation hγ hγ1 0) = circularPatchGrowingResponse := by
  have hs : HasDerivAt (fun s : ℝ => s • circularGrowingVariation hγ hγ1 0)
      (circularGrowingVariation hγ hγ1 0) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [Pi.smul_apply, id_eq, one_smul] using
      (hasDerivAt_id (0 : ℝ)).smul_const (circularGrowingVariation hγ hγ1 0 i)
  have hd : HasFDerivAt (circularFamilyPatchFourthMoment hγ hγ1.le)
      (fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1.le) 0)
      ((fun s : ℝ => s • circularGrowingVariation hγ hγ1 0) 0) := by
    simpa only [zero_smul] using
      (differentiableAt_circularFamilyPatchFourthMoment_zero hγ hγ1.le).hasFDerivAt
  have hc := hd.comp_hasDerivAt (0 : ℝ) hs
  change HasDerivAt (fun s : ℝ => circularFamilyPatchFourthMoment hγ hγ1.le
      (s • circularGrowingVariation hγ hγ1 0))
    (fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1.le) 0 (circularGrowingVariation hγ hγ1 0)) 0 at hc
  exact hc.unique (circularFamilyPatchFourthMoment_growing_hasDerivAt hγ hγ1)

theorem fderiv_circularFamilyPatchFourthMoment_growing_ne_zero {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    fderiv ℝ (circularFamilyPatchFourthMoment hγ hγ1.le) 0
      (circularGrowingVariation hγ hγ1 0) ≠ 0 := by
  rw [fderiv_circularFamilyPatchFourthMoment_growing]
  exact circularPatchGrowingResponse_ne_zero

end Euler2D

end
