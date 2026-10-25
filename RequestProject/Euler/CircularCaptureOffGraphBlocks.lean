module

public import RequestProject.Euler.CircularActualPartialGraphError
public import RequestProject.Euler.CircularCoRotatedCaptureSection
public import RequestProject.Euler.FiniteCaptureContinuousEnvelope

/-! The actual off-graph estimate holds at every time of a stopped
capture trajectory, including its first co-frame section inside a
block. Both the material clock and the original graph are preserved. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 6500

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

theorem circularCoRotationCLM_capture_block_add {γ : ℝ≥0} (n ℓ : ℕ) (u : ℝ)
    (Z : Fin 2 → LittleContourSpace γ) :
    circularCoRotationCLM γ ((n : ℝ) * circularCaptureBlockTime ℓ + u) Z =
      circularCoRotationCLM γ u Z := by
  calc
    _ = circularCoRotationCLM γ (u + (n : ℝ) * circularCaptureBlockTime ℓ) Z := by
      congr 1
      ring
    _ = circularCoRotationCLM γ u
        (circularCoRotationCLM γ ((n : ℝ) * circularCaptureBlockTime ℓ) Z) :=
      (circularCoRotationCLM_add γ u _ Z).symm
    _ = _ := by rw [circularCoRotationCLM_capture_grid]

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circular_capture_offGraph_block_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) {ℓ : ℕ} (hℓ : 0 < ℓ)
    {X : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : ContDiffAt ℝ 2 (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r x) :
    ∃ d > 0, d ≤ r / 2 ∧ ∃ rn > 0, ∃ E > 0,
      ∀ (y p : ℝ → Fin 2 → LittleContourSpace γ) (B : ℕ → ℝ) (N : ℕ) {D κ : ℝ},
        let T := circularCaptureBlockTime ℓ
        let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
        let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
        let v := fun n : ℕ => J (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
        let α := fun n => Q (v n)
        let w := fun n => v n - x (α n) 0
        0 < N → D ∈ Icc (0 : ℝ) ((N : ℝ) * T) → 0 ≤ κ →
        (∀ n < N, 0 ≤ B n) →
        (∀ n < N, (n : ℝ) * T ≤ D → circularConstrainedChart hγ hγ1 (v n) = y ((n : ℝ) * T)) →
        (∀ n < N, (n : ℝ) * T ≤ D → ‖α n‖ + ‖w n‖ ≤ d) →
        (∀ t ∈ Icc (0 : ℝ) D, HasDerivAt y (circularBanachField hγ hγ1 (y t) + p t) t) →
        (∀ t ∈ Icc (0 : ℝ) D, ‖y t - littleCircularMaterialContours hγ hγ1 t‖ ≤ rn) →
        (∀ n < N, ∀ u ∈ Icc (0 : ℝ) T, (n : ℝ) * T + u ≤ D →
          ‖p ((n : ℝ) * T + u)‖ ≤ B n + κ *
            ‖y ((n : ℝ) * T + u) - littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + u)‖) →
        ∀ t ∈ Icc (0 : ℝ) D, ∃ n < N, ∃ u ∈ Icc (0 : ℝ) T,
          t = (n : ℝ) * T + u ∧
          ‖J (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1) -
              x (Q (J (circularCoRotationCLM γ t (y t) - littleCircularReference hγ hγ1))) 0‖ ≤
            E * (‖w n‖ + B n + κ * rn) := by
  let T := circularCaptureBlockTime ℓ
  have hT : 0 < T := circularCaptureBlockTime_pos hℓ
  obtain ⟨d, hdpos, hdr, rn, hrn, E, hE, hpartial⟩ :=
    exists_circular_actual_partial_graph_error_constants hγ hγ1 hR hr hT hX hd hfix harea hg
  refine ⟨d, hdpos, hdr, rn, hrn, E, hE, ?_⟩
  intro y p B N D κ
  dsimp only
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let v := fun n : ℕ => J (y ((n : ℝ) * T) - littleCircularReference hγ hγ1)
  let α := fun n => Q (v n)
  let w := fun n => v n - x (α n) 0
  intro hN hD hκ hB hchart hsize hyd hnear hforce t ht
  obtain ⟨n, hn, u, hu, htime⟩ := exists_finite_capture_block_coordinates hT hN ⟨ht.1, ht.2.trans hD.2⟩
  have hnt : (n : ℝ) * T ≤ D := by linarith only [htime, ht.2, hu.1]
  let Hn := min T (D - (n : ℝ) * T)
  have hHn : Hn ∈ Icc (0 : ℝ) T :=
    ⟨le_min hT.le (sub_nonneg.mpr hnt), min_le_left _ _⟩
  have huHn : u ∈ Icc (0 : ℝ) Hn := by
    exact ⟨hu.1, le_min hu.2 (by linarith only [htime, ht.2])⟩
  have hlocaltime (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Hn) : (n : ℝ) * T + s ∈ Icc (0 : ℝ) D := by
    refine ⟨add_nonneg (mul_nonneg (Nat.cast_nonneg n) hT.le) hs.1, ?_⟩
    have hh := hs.2.trans (min_le_right T (D - (n : ℝ) * T))
    linarith only [hh]
  have hperiod : Function.Periodic (littleCircularMaterialContours hγ hγ1) T :=
    (periodic_littleCircularMaterialContours hγ hγ1).nat_mul (2 * ℓ)
  have hcshift (s : ℝ) : littleCircularMaterialContours hγ hγ1 ((n : ℝ) * T + s) =
      littleCircularMaterialContours hγ hγ1 s := by
    simpa only [add_comm] using (hperiod.nat_mul n) s
  have hα : Q (α n) = α n := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le (v n)
  have hi : y ((n : ℝ) * T + 0) = circularConstrainedChart hγ hγ1 (x (α n) 0 + w n) := by
    rw [add_zero, show x (α n) 0 + w n = v n by
      dsimp only [w]
      rw [← add_sub_assoc, add_sub_cancel_left]]
    exact (hchart n hn hnt).symm
  have hderiv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Hn) :
      HasDerivAt (fun z => y ((n : ℝ) * T + z))
        (circularBanachField hγ hγ1 (y ((n : ℝ) * T + s)) + p ((n : ℝ) * T + s)) s := by
    have hh := (hyd _ (hlocaltime s hs)).scomp s ((hasDerivAt_id s).const_add ((n : ℝ) * T))
    simpa only [one_smul] using hh
  have hnearLocal (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Hn) :
      ‖y ((n : ℝ) * T + s) - littleCircularMaterialContours hγ hγ1 s‖ ≤ rn := by
    have hh := hnear _ (hlocaltime s hs)
    rw [hcshift] at hh
    exact hh
  have hforceLocal (s : ℝ) (hs : s ∈ Icc (0 : ℝ) Hn) : ‖p ((n : ℝ) * T + s)‖ ≤ B n + κ * rn :=
    (hforce n hn s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩ (hlocaltime s hs).2).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hnear _ (hlocaltime s hs)) hκ))
  have hh := hpartial (α n) (w n) hα (hsize n hn hnt) hHn
    (show 0 ≤ B n + κ * rn by positivity [hB n hn])
    (fun z => y ((n : ℝ) * T + z)) (fun z => p ((n : ℝ) * T + z))
    hi hderiv hnearLocal hforceLocal u huHn
  refine ⟨n, hn, u, hu, htime, ?_⟩
  rw [htime, circularCoRotationCLM_capture_block_add]
  simpa only [add_assoc] using hh

end Euler2D

end
