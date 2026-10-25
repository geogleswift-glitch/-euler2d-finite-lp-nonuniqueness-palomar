module

public import RequestProject.Euler.TorusPhysicalLabelSourceContinuity
public import RequestProject.Euler.ComplexBiotSavartL1Continuity

/-! The true whole-plane Biot--Savart velocity of any bounded actual
Euler label is jointly continuous, including for discontinuous labels. -/

@[expose] public section

set_option maxHeartbeats 2500000

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem norm_physicalComplexLabelSource_le {w : R2 → ℝ} {M : ℝ}
    (hM : ∀ x, ‖w x‖ ≤ M) (t : ℝ) (z : ℂ) : ‖S.physicalComplexSource w t z‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  unfold physicalComplexSource boxedComplexDensity
  by_cases hz : complexTorusPoint z ∈ torusBox
  · rw [indicator_of_mem hz]
    exact hM _
  · rw [indicator_of_notMem hz, norm_zero]
    exact hM0

theorem continuous_physicalComplexLabelVelocity {w : R2 → ℝ} {M : ℝ}
    (hw : MemLp w 2 μT) (hM : ∀ x, ‖w x‖ ≤ M) :
    Continuous (fun p : ℝ × ℂ => velocityC (S.physicalComplexSource w p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have ht : Tendsto (fun q : ℝ × ℂ => q.1) (𝓝 p) (𝓝 p.1) := continuous_fst.continuousAt
  have hz : Tendsto (fun q : ℝ × ℂ => q.2) (𝓝 p) (𝓝 p.2) := continuous_snd.continuousAt
  exact tendsto_velocityC_apply_of_L1
    (fun q : ℝ × ℂ => S.integrable_physicalComplexLabelSource (hw.integrable (by norm_num)) q.1)
    (S.integrable_physicalComplexLabelSource (hw.integrable (by norm_num)) p.1)
    (fun q z => S.norm_physicalComplexLabelSource_le hM q.1 z)
    (S.norm_physicalComplexLabelSource_le hM p.1)
    (S.tendsto_physicalComplexSource_L1_of_memLp hw ht) hz

end BoundedEulerParticleSystem
end Euler2D

end
