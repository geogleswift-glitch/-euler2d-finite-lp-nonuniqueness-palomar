module

public import RequestProject.Euler.ContourPhaseVorticity
public import RequestProject.Euler.ContourPatchVelocityContinuityLimit
public import RequestProject.Euler.CircularPhasePatchVorticity

/-! The true phase-independent patch velocity is jointly continuous.
Each point uses an actual open phase chart, and the indicator density
agrees exactly on overlaps. No chart selection is assumed continuous. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal

namespace Euler2D

local instance (priority := 2000) phaseVelocityC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)
local instance (priority := 2000) phaseVelocityC1_space (γ : ℝ≥0) :
    NormedSpace ℝ (ContourC1Space γ) := Submodule.normedSpace (contourC1GraphSubmodule γ)

theorem continuous_phaseFiniteContourPatchVelocity
    {P : Type*} [TopologicalSpace P] {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) {Z : P → ι → ContourC1Space γ} (hZ : ∀ i, Continuous (fun p => Z p i))
    (Z₀ : ι → ContourC1Space γ) (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (hphase : ∀ p, ∃ b : ι → ℝ, ∀ i, ‖contourParameterShiftC1 (b i) (Z p i) - Z₀ i‖ < r i / 4) :
    Continuous (fun p : P × ℂ => velocityC (phaseFiniteContourPatchVorticity g (Z p.1)) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨b, hb⟩ := hphase p.1
  let U : Set (P × ℂ) := {q | ∀ i, ‖contourParameterShiftC1 (b i) (Z q.1 i) - Z₀ i‖ < r i / 4}
  have hU : IsOpen U := by
    have hi (i : ι) : IsOpen {q : P × ℂ |
        ‖contourParameterShiftC1 (b i) (Z q.1 i) - Z₀ i‖ < r i / 4} :=
      isOpen_lt (((contourParameterShiftC1CLM γ (b i)).continuous.comp
        ((hZ i).comp continuous_fst)).sub continuous_const).norm continuous_const
    simpa only [U, setOf_forall] using isOpen_iInter_of_finite hi
  have hp : p ∈ U := hb
  let W : U → ι → ContourC1Space γ := fun q i => contourParameterShiftC1 (b i) (Z q.val.1 i)
  have hW (i : ι) : Continuous (fun q : U => W q i) :=
    (contourParameterShiftC1CLM γ (b i)).continuous.comp
      ((hZ i).comp (continuous_fst.comp continuous_subtype_val))
  have hsmall (q : U) (i : ι) : ‖W q i - Z₀ i‖ ≤ r i / 4 := (q.property i).le
  have hc := continuous_finiteContourC1PatchVelocity g hW Z₀ r hr href hsmall
  have hrestrict : Continuous (U.restrict (fun q : P × ℂ =>
      velocityC (phaseFiniteContourPatchVorticity g (Z q.1)) q.2)) := by
    have he : U.restrict (fun q : P × ℂ => velocityC (phaseFiniteContourPatchVorticity g (Z q.1)) q.2) =
        (fun q : U => velocityC (finiteContourC1PatchVorticity g (W q) Z₀ r hr href (hsmall q)) q.val.2) := by
      funext q
      change velocityC (phaseFiniteContourPatchVorticity g (Z q.val.1)) q.val.2 = _
      rw [phaseFiniteContourPatchVorticity_eq_chart g (Z q.val.1) Z₀ r hr href b (hsmall q)]
    rw [he]
    have hj : Continuous (fun q : U => (q, q.val.2)) :=
      continuous_id.prodMk (continuous_snd.comp continuous_subtype_val)
    have hcomp := hc.comp (f := fun q : U => (q, q.val.2)) hj
    exact hcomp
  exact ((continuousWithinAt_iff_continuousAt_restrict _ hp).mpr
    hrestrict.continuousAt).continuousAt (hU.mem_nhds hp)

theorem continuous_circularPhasePatchVelocity {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) :
    Continuous (fun p : circularQuarterPhaseDomain hγ hγ1 × ℂ =>
      velocityC (circularPhasePatchVorticity p.1.val) p.2) := by
  apply continuous_phaseFiniteContourPatchVelocity circularContourStrengths
    (fun i => (LittleContourSpace.inclusion γ).continuous.comp
      ((continuous_apply i).comp continuous_subtype_val))
    (circularReferenceC1 hγ hγ1) circularContourRadii growingMoment_radius_pos
    (lift_circularReferenceC1 hγ hγ1)
  intro p
  obtain ⟨b, hb⟩ := p.property.2
  exact ⟨-b, hb⟩

end Euler2D

end
