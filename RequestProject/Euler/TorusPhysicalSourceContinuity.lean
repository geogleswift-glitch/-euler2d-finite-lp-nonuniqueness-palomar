module

public import RequestProject.Euler.ActualTorusContourSourceContinuity
public import RequestProject.Euler.LocalizedTorusComparison
public import RequestProject.Euler.CircularFiniteSourceSupport
public import RequestProject.Euler.TorusKernelTimeContinuity

/-! The entire actual transported torus density, placed at the physical
complex origin. Its temporal L1 continuity follows from the proved
particleCurlL2 continuity, including for discontinuous patch sources. -/

@[expose] public section

set_option maxHeartbeats 2000000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

def boxedComplexDensity (w : R2 → ℝ) (z : ℂ) : ℝ :=
  torusBox.indicator w (complexTorusPoint z)

theorem measurableEmbedding_complexTorusPoint : MeasurableEmbedding complexTorusPoint := by
  have hi : Isometry complexTorusPoint := by
    intro x y
    simpa only [complexTorusPoint, edist_add_right] using complexPhysicalPlane.isometry x y
  exact hi.isClosedEmbedding.measurableEmbedding

theorem integrable_boxedComplexDensity {w : R2 → ℝ} (hw : Integrable w μT) :
    Integrable (boxedComplexDensity w) :=
  measurePreserving_complexTorusPoint.integrable_comp_of_integrable
    ((integrable_indicator_iff measurableSet_torusBox).mpr hw)

theorem integral_boxedComplexDensity (w : R2 → ℝ) :
    (∫ z : ℂ, boxedComplexDensity w z) = ∫ x in torusBox, w x := by
  unfold boxedComplexDensity
  rw [measurePreserving_complexTorusPoint.integral_comp measurableEmbedding_complexTorusPoint,
    integral_indicator measurableSet_torusBox]

theorem integral_abs_boxedComplexDensity_sub (w v : R2 → ℝ) :
    (∫ z : ℂ, |boxedComplexDensity w z - boxedComplexDensity v z|) =
      ∫ x in torusBox, |w x - v x| := by
  have he : (fun z => |boxedComplexDensity w z - boxedComplexDensity v z|) =
      boxedComplexDensity (fun x => |w x - v x|) := by
    funext z
    simp only [boxedComplexDensity]
    by_cases hz : complexTorusPoint z ∈ torusBox <;> simp [hz]
  rw [he, integral_boxedComplexDensity]

theorem boxedComplexDensity_support {w : R2 → ℝ} {a : ℝ}
    (hs : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → w x = 0) :
    ∀ z, a < ‖z‖ → boxedComplexDensity w z = 0 := by
  intro z hz
  unfold boxedComplexDensity
  by_cases hx : complexTorusPoint z ∈ torusBox
  · rw [indicator_of_mem hx]
    exact hs _ hx (by simpa only [norm_complexTorusPoint_sub_center] using hz)
  · exact indicator_of_notMem hx _

theorem boxedComplexDensity_fourfold {w : R2 → ℝ} {a : ℝ} (ha1 : a < 1)
    (hs : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → w x = 0)
    (hy : ∀ x, w (torusQuarterTurn x) = w x) :
    ∀ z, boxedComplexDensity w (I * z) = boxedComplexDensity w z := by
  intro z
  by_cases hz : a < ‖z‖
  · rw [boxedComplexDensity_support hs z hz,
      boxedComplexDensity_support hs (I * z) (by simpa only [norm_mul, norm_I, one_mul] using hz)]
  · have hn : ‖z‖ < 1 := (not_lt.mp hz).trans_lt ha1
    have hx : complexTorusPoint z ∈ torusBox :=
      norm_sub_center_lt_one_mem_box (by simpa only [norm_complexTorusPoint_sub_center] using hn)
    have hix : complexTorusPoint (I * z) ∈ torusBox :=
      norm_sub_center_lt_one_mem_box (by simpa only [norm_complexTorusPoint_sub_center,
        norm_mul, norm_I, one_mul] using hn)
    simp only [boxedComplexDensity, indicator_of_mem hx, indicator_of_mem hix]
    exact (congrArg w (torusQuarterTurn_complexTorusPoint z)).symm.trans (hy _)

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

def physicalComplexSource (w : R2 → ℝ) (t : ℝ) : ℂ → ℝ :=
  boxedComplexDensity (S.transportedScalar w t)

theorem integrable_physicalComplexSource {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t : ℝ) :
    Integrable (S.physicalComplexSource w t) := by
  apply integrable_boxedComplexDensity
  exact ((Lp.memLp _).integrable (by norm_num)).congr
    (S.particleCurlL2_ae_transportedScalar hwf t)

theorem integral_physicalComplexSource {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t : ℝ) :
    (∫ z : ℂ, S.physicalComplexSource w t z) = ∫ x in torusBox, f x := by
  rw [physicalComplexSource, integral_boxedComplexDensity,
    ← integral_congr_ae (S.particleCurlL2_ae_transportedScalar hwf t), integral_particleCurlL2]

theorem physicalComplexSource_L1_sub_le {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t s : ℝ) :
    (∫ z : ℂ, |S.physicalComplexSource w t z - S.physicalComplexSource w s z|) ≤
      scalarL2L1Constant * ‖particleCurlL2 f S.backward S.backward_area t -
        particleCurlL2 f S.backward S.backward_area s‖ := by
  rw [physicalComplexSource, physicalComplexSource, integral_abs_boxedComplexDensity_sub]
  calc
    _ = ∫ x in torusBox, ‖(particleCurlL2 f S.backward S.backward_area t -
          particleCurlL2 f S.backward S.backward_area s) x‖ := by
      apply integral_congr_ae
      filter_upwards [S.particleCurlL2_ae_transportedScalar hwf t,
        S.particleCurlL2_ae_transportedScalar hwf s,
        Lp.coeFn_sub (particleCurlL2 f S.backward S.backward_area t)
          (particleCurlL2 f S.backward S.backward_area s)] with x ht hs he
      rw [he]
      change |S.transportedScalar w t x - S.transportedScalar w s x| =
        ‖particleCurlL2 f S.backward S.backward_area t x -
          particleCurlL2 f S.backward S.backward_area s x‖
      rw [ht, hs, Real.norm_eq_abs]
    _ ≤ _ := integral_norm_scalarL2_le _

theorem integral_abs_physicalComplexSource_le {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t : ℝ) :
    (∫ z : ℂ, |S.physicalComplexSource w t z|) ≤ scalarL2L1Constant * ‖f‖ := by
  have he : (fun z : ℂ => |S.physicalComplexSource w t z|) =
      boxedComplexDensity (fun x => |S.transportedScalar w t x|) := by
    funext z
    dsimp only [physicalComplexSource, boxedComplexDensity]
    by_cases hz : complexTorusPoint z ∈ torusBox <;> simp [hz]
  rw [he, integral_boxedComplexDensity]
  calc
    _ = ∫ x in torusBox, ‖particleCurlL2 f S.backward S.backward_area t x‖ := by
      apply integral_congr_ae
      filter_upwards [S.particleCurlL2_ae_transportedScalar hwf t] with x hx
      rw [hx, Real.norm_eq_abs]
    _ ≤ scalarL2L1Constant * ‖particleCurlL2 f S.backward S.backward_area t‖ :=
      integral_norm_scalarL2_le _
    _ = _ := by
      have harea : MeasurePreserving (torusWrap ∘ S.backward t) μT μT := S.backward_area t
      have hnorm : ‖particleCurlL2 f S.backward S.backward_area t‖ = ‖f‖ :=
        Lp.norm_compMeasurePreserving f harea
      exact congrArg (fun r : ℝ => scalarL2L1Constant * r) hnorm

theorem tendsto_physicalComplexSource_L1 {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    {α : Type*} {l : Filter α} {τ : α → ℝ} {s : ℝ} (hτ : Tendsto τ l (𝓝 s)) :
    Tendsto (fun t => ∫ z : ℂ, |S.physicalComplexSource w (τ t) z -
      S.physicalComplexSource w s z|) l (𝓝 0) := by
  have hc := ((continuous_particleCurlL2 f S.backward_area S.backward_continuous).tendsto s).comp hτ
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hc
  exact squeeze_zero (fun t => integral_nonneg (fun z => abs_nonneg _))
    (fun t => S.physicalComplexSource_L1_sub_le hwf (τ t) s)
    (by simpa only [Function.comp_def, mul_zero] using hn.const_mul scalarL2L1Constant)

theorem physicalComplexSource_support {w : R2 → ℝ} {a t : ℝ}
    (hs : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) :
    ∀ z, a < ‖z‖ → S.physicalComplexSource w t z = 0 :=
  boxedComplexDensity_support hs

theorem physicalComplexSource_fourfold (hS : IsFourfoldBoundedEulerParticleSystem S)
    {w : R2 → ℝ} (hwper : IsTorusPeriodic w) (hwrot : ∀ x, w (torusQuarterTurn x) = w x)
    {a t : ℝ} (ha1 : a < 1) (ht : t ∈ Icc (0 : ℝ) T)
    (hs : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) :
    ∀ z, S.physicalComplexSource w t (I * z) = S.physicalComplexSource w t z :=
  boxedComplexDensity_fourfold ha1 hs (S.transportedScalar_quarterTurn hS hwper hwrot t ht)

theorem physicalComplexSource_fourthAbsoluteMoment_le {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) {a t : ℝ}
    (hs : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) :
    (∫ z : ℂ, ‖z‖ ^ 4 * |S.physicalComplexSource w t z|) ≤
      a ^ 4 * (scalarL2L1Constant * ‖f‖) :=
  (fourth_le_mass (S.integrable_physicalComplexSource hwf t)
    (S.physicalComplexSource_support hs)).trans
      (mul_le_mul_of_nonneg_left (S.integral_abs_physicalComplexSource_le hwf t) (by positivity))

end BoundedEulerParticleSystem

end Euler2D

end
