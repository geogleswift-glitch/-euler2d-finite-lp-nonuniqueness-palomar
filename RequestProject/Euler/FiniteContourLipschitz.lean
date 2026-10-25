module

public import Mathlib

/-! Finite products and actual finite weighted sums of locally Lipschitz
maps, for assembling finite contour families. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped NNReal BigOperators

namespace Euler2D

theorem locallyLipschitz_finite_pi {ι X Y : Type*} [Fintype ι]
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (f : ι → X → Y)
    (hf : ∀ i, LocallyLipschitz (f i)) : LocallyLipschitz (fun x i => f i x) := by
  classical
  intro x
  choose K V hV hLip using fun i => hf i x
  let C : ℝ≥0 := ∑ i, K i
  refine ⟨C, ⋂ i, V i, Filter.iInter_mem.mpr hV, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  apply (dist_pi_le_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mpr
  intro i
  have hKi : K i ≤ C :=
    Finset.single_le_sum (fun j _ => (show 0 ≤ K j from zero_le)) (Finset.mem_univ i)
  exact ((hLip i).dist_le_mul a (mem_iInter.mp ha i) b (mem_iInter.mp hb i)).trans
    (mul_le_mul_of_nonneg_right (show (K i : ℝ) ≤ (C : ℝ) from hKi) dist_nonneg)

def finiteContourWeightedSum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ι → ℝ) : (ι → E) →L[ℝ] E :=
  ∑ i, g i • ContinuousLinearMap.proj i

@[simp] theorem finiteContourWeightedSum_apply {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ι → ℝ) (z : ι → E) :
    finiteContourWeightedSum g z = ∑ i, g i • z i := by
  simp only [finiteContourWeightedSum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply]

theorem locallyLipschitz_finite_weighted_sum {ι X E : Type*} [Fintype ι]
    [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ι → ℝ) (f : ι → X → E) (hf : ∀ i, LocallyLipschitz (f i)) :
    LocallyLipschitz (fun x => ∑ i, g i • f i x) := by
  have h := (finiteContourWeightedSum (E := E) g).lipschitz.locallyLipschitz.comp
    (locallyLipschitz_finite_pi f hf)
  simpa only [Function.comp_def, finiteContourWeightedSum_apply] using h

end Euler2D

end
