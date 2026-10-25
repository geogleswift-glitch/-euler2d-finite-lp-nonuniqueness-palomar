module

public import RequestProject.Euler.ContourPhaseVelocityContinuity
public import RequestProject.Euler.WeakDivergenceHomeomorphFlow

/-! The actual phase-independent circular patch velocity generates
a genuine area-preserving complex homeomorphism flow. Its smooth
incompressible approximations and all uniform bounds are constructed. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

theorem integral_abs_circularPhasePatchVorticity_le {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {Z : Fin 2 → LittleContourSpace γ}
    (hZ : Z ∈ circularQuarterPhaseDomain hγ hγ1) :
    (∫ x, |circularPhasePatchVorticity Z x|) ≤
      finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  obtain ⟨b, hb⟩ := exists_circularQuarterPhase_shift hγ hγ1 hZ
  exact integral_abs_phaseFiniteContourPatchVorticity_le circularContourStrengths (fun i => (Z i).val)
    (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1) b hb

def circularPhaseVelocityOnInterval {γ : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (Z : Icc (0 : ℝ) T → Fin 2 → LittleContourSpace γ) (t : ℝ) : ℂ → ℂ :=
  velocityC (circularPhasePatchVorticity (Z (projIcc 0 T hT t)))

theorem circularPhaseVelocityOnInterval_of_mem {γ : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (Z : Icc (0 : ℝ) T → Fin 2 → LittleContourSpace γ) (t : Icc (0 : ℝ) T) (x : ℂ) :
    circularPhaseVelocityOnInterval hT Z t x = velocityC (circularPhasePatchVorticity (Z t)) x := by
  simp only [circularPhaseVelocityOnInterval, projIcc_val]

section Flow

variable {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {T : ℝ} (hT : 0 ≤ T)
  (Z : Icc (0 : ℝ) T → Fin 2 → LittleContourSpace γ)
  (hZ : Continuous Z) (hZm : ∀ t, Z t ∈ circularQuarterPhaseDomain hγ hγ1)

include hγ hγ1 hZ hZm

theorem continuous_circularPhaseVelocityOnInterval :
    Continuous (Function.uncurry (circularPhaseVelocityOnInterval hT Z)) := by
  let j : ℝ × ℂ → circularQuarterPhaseDomain hγ hγ1 × ℂ := fun p =>
    (⟨Z (projIcc 0 T hT p.1), hZm _⟩, p.2)
  have hj : Continuous j := ((hZ.comp ((continuous_projIcc (h := hT)).comp continuous_fst)).subtype_mk
    (fun p => hZm _)).prodMk continuous_snd
  exact (continuous_circularPhasePatchVelocity hγ hγ1).comp (f := j) hj

theorem norm_circularPhaseVelocityOnInterval_le (t : ℝ) (x : ℂ) :
    ‖circularPhaseVelocityOnInterval hT Z t x‖ ≤ finiteContourPatchSupBound circularContourStrengths +
      finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
  let s := projIcc 0 T hT t
  have hb := velocity_bound_split (integrable_circularPhasePatchVorticity hγ hγ1 (hZm s))
    (abs_circularPhasePatchVorticity_le hγ hγ1 (hZm s)) x (d := 1) (by norm_num)
  have hA := integral_abs_circularPhasePatchVorticity_le hγ hγ1 (hZm s)
  have hi : 0 ≤ ∫ y, |circularPhasePatchVorticity (Z s) y| := integral_nonneg (fun y => abs_nonneg _)
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  simp only [mul_one] at hb
  exact hb.trans (add_le_add le_rfl ((div_le_self hi hπ).trans hA))

theorem circularPhaseVelocityOnInterval_logFlowModulus_le
    (t : ℝ) {x y : ℂ} (hxy : ‖x - y‖ ≤ 1 / 2) :
    ‖circularPhaseVelocityOnInterval hT Z t x - circularPhaseVelocityOnInterval hT Z t y‖ ≤
      (8 * (finiteContourPatchSupBound circularContourStrengths +
        finiteContourPatchMassBound circularContourStrengths circularContourRadii)) * logFlowModulus ‖x - y‖ :=
  velocityC_logFlowModulus_le (integrable_circularPhasePatchVorticity hγ hγ1 (hZm _))
    (abs_circularPhasePatchVorticity_le hγ hγ1 (hZm _))
    (integral_abs_circularPhasePatchVorticity_le hγ hγ1 (hZm _)) hxy

theorem exists_circularPhase_particleFlow_area :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a, HasDerivAt (fun s => F s a)
        (circularPhaseVelocityOnInterval hT Z t (F t a)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume := by
  have hB : 0 ≤ finiteContourPatchSupBound circularContourStrengths +
      finiteContourPatchMassBound circularContourStrengths circularContourRadii := by
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  let M : ℝ≥0 := ⟨_, hB⟩
  let C : ℝ≥0 := ⟨8 * (M : ℝ), by positivity⟩
  apply exists_complex_measurePreserving_logHomeomorphFlow (M := M) (C := C)
    (continuous_circularPhaseVelocityOnInterval hγ hγ1 hT Z hZ hZm)
    (norm_circularPhaseVelocityOnInterval_le hγ hγ1 hT Z hZ hZm)
    (fun t _ _ hxy => circularPhaseVelocityOnInterval_logFlowModulus_le hγ hγ1 hT Z hZ hZm t hxy) _ hT
  intro t
  apply isPlanarWeaklyDivergenceFree_velocityC (integrable_circularPhasePatchVorticity hγ hγ1 (hZm _))
  intro z
  simpa only [Real.norm_eq_abs] using abs_circularPhasePatchVorticity_le hγ hγ1 (hZm _) z

end Flow

end Euler2D

end
