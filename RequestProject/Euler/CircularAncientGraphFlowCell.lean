module

public import RequestProject.Euler.CircularBackwardGraphWindowInvariance
public import RequestProject.Euler.CircularCoRotatedFlowEndpoints

/-! Between actual ancient samples, uniqueness identifies the whole
material cell with the actual extended flow. Every intermediate point
then lies on the same already fixed backward graph in its true frame. -/

@[expose] public section

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_same_circularBackwardGraph_actual_cell_radius {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {D R S r w : ℝ}
    (hD : 0 < D) (hR : 0 < R) (hS : 0 < S) (hr : 0 < r) (hw : 1 ≤ w)
    {X Y : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hX : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) R) period X)
    (hd : DifferentiableAt ℝ (fun W => X W period) (littleCircularReference hγ hγ1))
    (hfix : X (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (hareaX : ∀ W ∈ ball (littleCircularReference hγ hγ1) R, ∀ i,
      littleContourArea γ (X W period i) = littleContourArea γ (W i))
    (hY : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) S) (D + period) Y)
    (hareaY : ∀ W ∈ ball (littleCircularReference hγ hγ1) S, ∀ t ∈ Icc (0 : ℝ) (D + period), ∀ i,
      littleContourArea γ (Y W t i) = littleContourArea γ (W i))
    {x : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => X W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) w r x) :
    ∃ η > 0, η ≤ r / 2 ∧ ∃ C > 0,
      ∀ A : ℝ → Fin 2 → LittleContourSpace γ, ContinuousOn A (Iic (0 : ℝ)) →
      (∀ t ≤ 0, A t ∈ circularBanachDomain hγ hγ1) →
      (∀ t ≤ 0, HasDerivAt A (circularBanachField hγ hγ1 (A t)) t) →
      ∀ a : ℝ, a + D ≤ 0 → ∀ ξ : CircularConstrainedTangentSpace γ,
      circularConstrainedUnstableProjectionCLM hγ hγ1.le ξ = ξ → ‖ξ‖ ≤ η →
      A a = circularConstrainedChart hγ hγ1 (x ξ 0) → ∀ u ∈ Icc (0 : ℝ) D,
      ∃ α : CircularConstrainedTangentSpace γ,
        circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧
        ‖α‖ ≤ r / 2 ∧ ‖α‖ ≤ C * ‖ξ‖ ∧
        circularConstrainedChart hγ hγ1 (x α 0) = circularCoRotationCLM γ u (A (a + u)) := by
  let P := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨b, hb, hbr, hinv⟩ := exists_same_circularBackwardGraph_window_invariant_radius
    hγ hγ1 hD hR hS hr hw hX hd hfix hareaX hY hareaY hg
  obtain ⟨ν, hν, Cf, hCf, hcoords⟩ := exists_circularCoRotatedFlow_uniform_constraint_coordinates
    hγ hγ1 (add_pos hD hp) hS (by norm_num : (0 : ℝ) < 1) hY hareaY
  let η := min b (ν / 4)
  have hη : 0 < η := lt_min hb (by positivity)
  have hηr : η ≤ r / 2 := (min_le_left _ _).trans hbr
  have hdom : IsOpen (circularBanachDomain hγ hγ1) := by
    unfold circularBanachDomain
    exact isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) := by
    unfold circularBanachField circularBanachDomain
    exact contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1
  refine ⟨η, hη, hηr, 2 * (‖P‖ + 1) * Cf, by positivity, ?_⟩
  intro A hAc hAm hAd a ha ξ hξ hξη hinit u hu
  have hξr : ‖ξ‖ ≤ r / 2 := hξη.trans hηr
  let v := x ξ 0
  have hv : ‖v‖ ≤ 2 * ‖ξ‖ := by
    simpa only [pow_zero, mul_one] using hg.norm_le ξ hξ hξr 0
  have hvν : ‖v‖ < ν := by
    have hh : ‖ξ‖ ≤ ν / 4 := hξη.trans (min_le_right _ _)
    nlinarith
  have hcv := hcoords v hvν
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : a + t ≤ 0 := by linarith [ht.2]
  have htimeY (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) : t ∈ Icc (0 : ℝ) (D + period) :=
    ⟨ht.1, by linarith [ht.2]⟩
  have hshiftc : ContinuousOn (fun t => A (a + t)) (Icc (0 : ℝ) D) :=
    hAc.comp (continuous_const.add continuous_id).continuousOn htime
  have hshiftd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) :
      HasDerivAt (fun s => A (a + s)) (circularBanachField hγ hγ1 (A (a + t))) t := by
    have hh := (hAd (a + t) (htime t ht)).scomp t
      ((hasDerivAt_const t a).add (hasDerivAt_id t))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_smul] using hh
  have htraj : EqOn (fun t => A (a + t)) (Y (circularConstrainedChart hγ hγ1 v)) (Icc (0 : ℝ) D) := by
    apply eqOn_of_banachODE_open hdom hf hshiftc
      ((hY.continuous _ hcv.1).mono (Icc_subset_Icc_right (by linarith : D ≤ D + period)))
      (fun t ht => hAm _ (htime t ht)) (fun t ht => hY.mem _ hcv.1 t (htimeY t ht))
      (fun t ht => hshiftd t ⟨ht.1, ht.2.le⟩)
      (fun t ht => hY.hasDerivAt _ hcv.1 t (htimeY t ⟨ht.1, ht.2.le⟩))
    change A (a + 0) = Y (circularConstrainedChart hγ hγ1 (x ξ 0)) 0
    rw [add_zero, hinit, hY.initial _ hcv.1]
  have hi := hinv u hu ξ hξ (hξη.trans (min_le_left _ _))
  let z := circularCoRotatedConstrainedMap hγ hγ1 Y u v
  let α := P z
  have hα : P α = α := circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le z
  refine ⟨α, hα, hi.1, ?_, ?_⟩
  · have hz : ‖z‖ ≤ Cf * ‖v‖ := (hcv.2 u (htimeY u hu)).2.1
    calc
      ‖α‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (Cf * ‖v‖) := mul_le_mul_of_nonneg_left hz (norm_nonneg P)
      _ ≤ ‖P‖ * (Cf * (2 * ‖ξ‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv hCf.le) (norm_nonneg P)
      _ ≤ (2 * (‖P‖ + 1) * Cf) * ‖ξ‖ := by
        nlinarith [mul_nonneg hCf.le (norm_nonneg ξ)]
  · have hx : x α 0 = z := congrFun hi.2 0
    have hchart : circularConstrainedChart hγ hγ1 z =
        circularCoRotationCLM γ u (Y (circularConstrainedChart hγ hγ1 v) u) :=
      (hcv.2 u (htimeY u hu)).2.2
    rw [hx, hchart]
    exact congrArg (circularCoRotationCLM γ u) (htraj hu).symm

end Euler2D

end
