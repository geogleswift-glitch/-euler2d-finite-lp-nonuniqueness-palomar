module

public import RequestProject.Euler.ActualTorusContourFieldBudget

/-! Exact conservation of the full physical source L1 mass. This retains
the spatial scaling of the periodic cancellation budget. -/

@[expose] public section

set_option maxHeartbeats 1700000

noncomputable section

open Complex ComplexConjugate Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

theorem integral_abs_particleCurlL2 (f : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    (∫ x in torusBox, |particleCurlL2 f Y hY t x|) = ∫ x in torusBox, |f x| := by
  calc
    _ = ∫ x in torusBox, |f (torusWrap (Y t x))| := by
      apply integral_congr_ae
      filter_upwards [particleCurlL2_ae f Y hY t] with x hx
      rw [hx]
    _ = ∫ x, |f x| ∂Measure.map (torusWrap ∘ Y t) μT :=
      (integral_map (hY t).aemeasurable
        (by rw [(hY t).map_eq]; exact (Lp.aestronglyMeasurable f).norm)).symm
    _ = _ := by rw [(hY t).map_eq]

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem integral_abs_physicalComplexSource {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) (t : ℝ) :
    (∫ z : ℂ, |S.physicalComplexSource w t z|) = ∫ x in torusBox, |f x| := by
  have he : (fun z : ℂ => |S.physicalComplexSource w t z|) =
      boxedComplexDensity (fun x => |S.transportedScalar w t x|) := by
    funext z
    dsimp only [physicalComplexSource, boxedComplexDensity]
    by_cases hz : complexTorusPoint z ∈ torusBox <;> simp [hz]
  rw [he, integral_boxedComplexDensity]
  calc
    _ = ∫ x in torusBox, |particleCurlL2 f S.backward S.backward_area t x| := by
      apply integral_congr_ae
      filter_upwards [S.particleCurlL2_ae_transportedScalar hwf t] with x hx
      rw [hx]
    _ = _ := integral_abs_particleCurlL2 f S.backward S.backward_area t

theorem physicalComplexSource_fourthAbsoluteMoment_le_initialL1 {w : R2 → ℝ}
    (hwf : w =ᵐ[μT] (f : R2 → ℝ)) {a t : ℝ}
    (hs : ∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) :
    (∫ z : ℂ, ‖z‖ ^ 4 * |S.physicalComplexSource w t z|) ≤
      a ^ 4 * ∫ x in torusBox, |f x| := by
  have hh := fourth_le_mass (S.integrable_physicalComplexSource hwf t)
    (S.physicalComplexSource_support hs)
  rwa [S.integral_abs_physicalComplexSource hwf t] at hh

theorem exists_physicalComplexSource_contourLittle_initialL1_budget
    {a : ℝ} (ha : 0 < a) (ha16 : a ≤ 1 / 16) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ : ℝ≥0}, (γ : ℝ) ≤ 1 →
      ∀ (hS : IsFourfoldBoundedEulerParticleSystem S) (w : R2 → ℝ),
      w =ᵐ[μT] (f : R2 → ℝ) → IsTorusPeriodic w →
      (∀ x, w (torusQuarterTurn x) = w x) → (∫ x in torusBox, f x) = 0 →
      ∀ t ∈ Icc (0 : ℝ) T,
      (∀ x ∈ torusBox, a < ‖x - torusCenter‖ → S.transportedScalar w t x = 0) →
      ∀ {R L : ℝ}, 0 < R → 0 ≤ L → (L + 1) * R ≤ a / 2 →
      ∀ Z : LittleContourSpace γ, ‖Z‖ ≤ L * R →
      ∀ Q : LittleContourSpace γ,
        (∀ θ, LittleContourSpace.lift γ Q θ =
          actualTorusCorrectionVelocity (S.physicalComplexSource w t)
            (LittleContourSpace.lift γ Z θ)) →
        ‖Q‖ / R ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
          a ^ 4 * ∫ x in torusBox, |f x| := by
  obtain ⟨C, hC, hbudget⟩ := exists_actualTorusCorrection_contourLittle_budget ha ha16
  refine ⟨C, hC, ?_⟩
  intro γ hγ hS w hwf hwper hwrot hmean t ht hs R L hR hL hsmall Z hZ Q hQ
  have hh := hbudget hγ (S.physicalComplexSource w t)
    (S.integrable_physicalComplexSource hwf t) (S.physicalComplexSource_support hs)
    ((S.integral_physicalComplexSource hwf t).trans hmean)
    (S.physicalComplexSource_fourfold hS hwper hwrot (by linarith) ht hs)
    hR hL hsmall Z hZ Q hQ
  have hB : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
    unfold torusCorrectionContourBudget
    positivity
  refine hh.trans ?_
  have hm := S.physicalComplexSource_fourthAbsoluteMoment_le_initialL1 hwf hs
  calc
    _ ≤ C * torusCorrectionContourBudget (γ : ℝ) L * R ^ 2 *
        (a ^ 4 * ∫ x in torusBox, |f x|) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end BoundedEulerParticleSystem

end Euler2D

end
