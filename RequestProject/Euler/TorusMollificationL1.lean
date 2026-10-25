module

public import RequestProject.Euler.TorusKernelMollification

/-! Actual mass-preserving kernel averaging and its uniform `L¹` estimates. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric Real
open scoped ContDiff ENNReal

namespace Euler2D

def torusKernelAverage (w : R2 → ℝ) (g : R2 → R2) (x : R2) : R2 :=
  ∫ y in torusBox, w y • g (x - y + torusCenter)

lemma integrable_periodicKernel_sub_left {g : R2 → R2}
    (hg : Integrable g μT) (hp : IsTorusPeriodic g) (x : R2) :
    Integrable (fun y => g (x - y + torusCenter)) μT := by
  convert (torusAreaPreserving_sub_left (x + torusCenter)).integrable_comp hg hp using 1
  funext y
  congr 1
  abel

lemma integral_norm_periodicKernel_sub_left {g : R2 → R2}
    (hg : Integrable g μT) (hp : IsTorusPeriodic g) (x : R2) :
    (∫ y in torusBox, ‖g (x - y + torusCenter)‖) = ∫ y in torusBox, ‖g y‖ := by
  convert (torusAreaPreserving_sub_left (x + torusCenter)).integral_comp
    hg.norm.aestronglyMeasurable (fun y i => congrArg norm (hp y i)) using 1
  congr 1
  funext y
  congr 2
  abel

lemma integral_norm_periodicKernel_shift {g : R2 → R2}
    (hg : Integrable g μT) (hp : IsTorusPeriodic g) (y : R2) :
    (∫ x in torusBox, ‖g (x - y + torusCenter)‖) = ∫ x in torusBox, ‖g x‖ := by
  convert (torusAreaPreserving_add_right (torusCenter - y)).integral_comp
    hg.norm.aestronglyMeasurable (fun x i => congrArg norm (hp x i)) using 1
  congr 1
  funext x
  congr 2
  abel

lemma integrable_periodicKernel_prod {g : R2 → R2}
    (hg : Integrable g μT) (hgm : Measurable g) (hp : IsTorusPeriodic g) :
    Integrable (fun p : R2 × R2 => g (p.1 - p.2 + torusCenter)) (μT.prod μT) := by
  have hm : Measurable (fun p : R2 × R2 => g (p.1 - p.2 + torusCenter)) :=
    hgm.comp ((measurable_fst.sub measurable_snd).add measurable_const)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (integrable_periodicKernel_sub_left hg hp), ?_⟩
  apply (integrable_const (∫ y in torusBox, ‖g y‖)).congr
  exact Eventually.of_forall fun x => (integral_norm_periodicKernel_sub_left hg hp x).symm

lemma integrable_torusKernelAverage_prod {w : R2 → ℝ} {g : R2 → R2}
    (hw : Continuous w) (hg : Integrable g μT) (hgm : Measurable g)
    (hp : IsTorusPeriodic g) :
    Integrable (fun p : R2 × R2 => w p.2 • g (p.1 - p.2 + torusCenter))
      (μT.prod μT) := by
  obtain ⟨M, hM⟩ := bound_on_box hw
  apply (integrable_periodicKernel_prod hg hgm hp).bdd_smul M
    (hw.measurable.comp measurable_snd).aestronglyMeasurable
  have hb : ∀ᵐ y ∂μT, ‖w y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
    simpa only [Real.norm_eq_abs] using hM y hy
  exact Measure.quasiMeasurePreserving_snd.ae hb

theorem integral_norm_torusKernelAverage_le {w : R2 → ℝ} {g : R2 → R2}
    (hw : Continuous w) (hw0 : ∀ y, 0 ≤ w y)
    (hg : Integrable g μT) (hgm : Measurable g) (hp : IsTorusPeriodic g) :
    (∫ x in torusBox, ‖torusKernelAverage w g x‖) ≤
      (∫ y in torusBox, w y) * ∫ x in torusBox, ‖g x‖ := by
  have hprod := integrable_torusKernelAverage_prod hw hg hgm hp
  have hnorm (y : R2) : (∫ x in torusBox, ‖w y • g (x - y + torusCenter)‖) =
      w y * ∫ x in torusBox, ‖g x‖ := by
    simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 y)]
    rw [integral_const_mul, integral_norm_periodicKernel_shift hg hp]
  calc
    _ ≤ ∫ x in torusBox, ∫ y in torusBox, ‖w y • g (x - y + torusCenter)‖ := by
      apply integral_mono hprod.integral_prod_left.norm hprod.integral_norm_prod_left
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ y in torusBox, ∫ x in torusBox, ‖w y • g (x - y + torusCenter)‖ :=
      integral_integral_swap hprod.norm
    _ = (∫ y in torusBox, w y) * ∫ x in torusBox, ‖g x‖ := by
      simp_rw [hnorm]
      exact integral_mul_const _ _

theorem integral_norm_regularizedTorusKernel_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x in torusBox, ‖regularizedTorusKernel ε hε x‖) ≤
      ∫ x in torusBox, ‖torusBiotSavartKernel x‖ := by
  have h := integral_norm_torusKernelAverage_le
    (torusKernelMollifier_test hε hε1).1.continuous (torusKernelMollifier_nonneg ε hε)
    integrable_torusBiotSavartKernel measurable_torusBiotSavartKernel
    isTorusPeriodic_torusBiotSavartKernel
  change (∫ x in torusBox,
    ‖torusKernelAverage (torusKernelMollifier ε hε) torusBiotSavartKernel x‖) ≤
      ∫ x in torusBox, ‖torusBiotSavartKernel x‖
  simpa only [torusKernelMollifier_integral hε hε1, one_mul] using h

lemma regularizedTorusKernel_sub_eq_average {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x h : R2) :
    regularizedTorusKernel ε hε (x + h) - regularizedTorusKernel ε hε x =
      torusKernelAverage (torusKernelMollifier ε hε)
        (fun z => torusBiotSavartKernel (z + h) - torusBiotSavartKernel z) x := by
  have hw := (torusKernelMollifier_test hε hε1).1.continuous
  obtain ⟨M, hM⟩ := bound_on_box hw
  have hb : ∀ᵐ y ∂μT, ‖torusKernelMollifier ε hε y‖ ≤ M := by
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with y hy
    simpa only [Real.norm_eq_abs] using hM y hy
  change (∫ y in torusBox, torusKernelMollifier ε hε y •
      torusBiotSavartKernel (x + h - y + torusCenter)) -
    (∫ y in torusBox, torusKernelMollifier ε hε y •
      torusBiotSavartKernel (x - y + torusCenter)) = _
  rw [← integral_sub (integrable_torusKernelVelocity_integrand hw.aestronglyMeasurable hb (x + h))
    (integrable_torusKernelVelocity_integrand hw.aestronglyMeasurable hb x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only [torusKernelAverage]
    rw [← smul_sub]
    congr 2
    abel

theorem integral_norm_regularizedTorusKernel_translation_le {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (h : R2) :
    (∫ x in torusBox, ‖regularizedTorusKernel ε hε (x + h) - regularizedTorusKernel ε hε x‖) ≤
      torusKernelTranslationError h := by
  let g := fun z => torusBiotSavartKernel (z + h) - torusBiotSavartKernel z
  have hgm : Measurable g :=
    (measurable_torusBiotSavartKernel.comp (measurable_id.add_const h)).sub
      measurable_torusBiotSavartKernel
  have hgp : IsTorusPeriodic g := by
    intro x i
    dsimp only [g]
    have he : x + EuclideanSpace.single i (2 * π) + h =
        (x + h) + EuclideanSpace.single i (2 * π) := by abel
    rw [he, isTorusPeriodic_torusBiotSavartKernel, isTorusPeriodic_torusBiotSavartKernel]
  have heq := regularizedTorusKernel_sub_eq_average hε hε1
  simp_rw [heq]
  have hb := integral_norm_torusKernelAverage_le
    (torusKernelMollifier_test hε hε1).1.continuous (torusKernelMollifier_nonneg ε hε)
    (integrable_torusBiotSavartKernel_translation_difference h) hgm hgp
  unfold torusKernelTranslationError
  simpa only [torusKernelMollifier_integral hε hε1, one_mul] using hb

theorem exists_uniform_regularizedKernel_translation_le_logFlowModulus :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ h : R2, ‖h‖ ≤ 1 / 2 →
      (∫ x in torusBox, ‖regularizedTorusKernel ε hε (x + h) -
        regularizedTorusKernel ε hε x‖) ≤ C * logFlowModulus ‖h‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_torusKernelTranslationError_le_logFlowModulus
  exact ⟨C, hC, fun ε hε hε1 h hh =>
    (integral_norm_regularizedTorusKernel_translation_le hε hε1 h).trans (hbound h hh)⟩

end Euler2D

end
