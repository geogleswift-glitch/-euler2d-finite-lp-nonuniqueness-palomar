module

public import RequestProject.Euler.BanachBackwardSegments

/-! Compatible actual return segments stabilize on every bounded
time interval and define a genuine ancient integral curve. -/

@[expose] public section

set_option maxHeartbeats 1500000

noncomputable section

open Set Filter Topology Metric

namespace Euler2D

theorem exists_backward_time_index {T : ℝ} (hT : 0 < T) (t : ℝ) :
    ∃ n : ℕ, -(n : ℝ) * T < t := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-t / T)
  refine ⟨n, ?_⟩
  have he := (div_lt_iff₀ hT).mp hn
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def banachAncientCurve {T : ℝ} (hT : 0 < T) (X : E → ℝ → E) (z : ℕ → E) (t : ℝ) : E :=
  banachBackwardSegment X T z (Classical.choose (exists_backward_time_index hT t)) t

section ActualFlow

variable {f : E → E} {U V : Set E} {T : ℝ} {X : E → ℝ → E} {z : ℕ → E}
variable (hT : 0 < T) (hX : IsBanachFlowOn f U V T X) (hz : ∀ n, z n ∈ V)
variable (hreturn : ∀ n, X (z (n + 1)) T = z n)

include hT hX hz hreturn

theorem banachAncientCurve_eq_segment (n : ℕ) {t : ℝ} (ht : -(n : ℝ) * T ≤ t) :
    banachAncientCurve hT X z t = banachBackwardSegment X T z n t := by
  let m := Classical.choose (exists_backward_time_index hT t)
  have hm : -(m : ℝ) * T < t := Classical.choose_spec (exists_backward_time_index hT t)
  change banachBackwardSegment X T z m t = banachBackwardSegment X T z n t
  rcases le_total m n with hmn | hnm
  · exact (banachBackwardSegment_agrees hT hX hz hreturn hmn hm.le).symm
  · exact banachBackwardSegment_agrees hT hX hz hreturn hnm ht

theorem banachAncientCurve_hasDerivAt {t : ℝ} (ht : t ≤ 0) :
    HasDerivAt (banachAncientCurve hT X z) (f (banachAncientCurve hT X z t)) t := by
  obtain ⟨n, hn⟩ := exists_backward_time_index hT t
  have he : banachAncientCurve hT X z =ᶠ[𝓝 t] banachBackwardSegment X T z n := by
    filter_upwards [Ioi_mem_nhds hn] with s hs
    exact banachAncientCurve_eq_segment hT hX hz hreturn n hs.le
  have hd := banachBackwardSegment_hasDerivAt hT hX hz hreturn n ⟨hn.le, ht⟩
  rw [banachAncientCurve_eq_segment hT hX hz hreturn n hn.le]
  exact hd.congr_of_eventuallyEq he

theorem banachAncientCurve_mem {t : ℝ} (ht : t ≤ 0) : banachAncientCurve hT X z t ∈ U := by
  obtain ⟨n, hn⟩ := exists_backward_time_index hT t
  rw [banachAncientCurve_eq_segment hT hX hz hreturn n hn.le]
  exact banachBackwardSegment_mem hT hX hz hreturn n ⟨hn.le, ht⟩

theorem banachAncientCurve_sample (n : ℕ) : banachAncientCurve hT X z (-(n : ℝ) * T) = z n := by
  rw [banachAncientCurve_eq_segment hT hX hz hreturn n le_rfl,
    banachBackwardSegment_left hT hX hz]

theorem banachAncientCurve_zero : banachAncientCurve hT X z 0 = z 0 := by
  simpa only [Nat.cast_zero, neg_zero, zero_mul] using banachAncientCurve_sample hT hX hz hreturn 0

theorem continuousOn_banachAncientCurve : ContinuousOn (banachAncientCurve hT X z) (Iic 0) := by
  intro t ht
  exact (banachAncientCurve_hasDerivAt hT hX hz hreturn ht).continuousAt.continuousWithinAt

theorem exists_ancientCurve_of_return_sequence :
    ∃ Y : ℝ → E, Y 0 = z 0 ∧ ContinuousOn Y (Iic 0) ∧
      (∀ t ≤ 0, Y t ∈ U) ∧
      (∀ t ≤ 0, HasDerivAt Y (f (Y t)) t) ∧
      ∀ n : ℕ, Y (-(n : ℝ) * T) = z n := by
  exact ⟨banachAncientCurve hT X z, banachAncientCurve_zero hT hX hz hreturn,
    continuousOn_banachAncientCurve hT hX hz hreturn,
    fun _ ht => banachAncientCurve_mem hT hX hz hreturn ht,
    fun _ ht => banachAncientCurve_hasDerivAt hT hX hz hreturn ht,
    banachAncientCurve_sample hT hX hz hreturn⟩

end ActualFlow

end Euler2D

end
