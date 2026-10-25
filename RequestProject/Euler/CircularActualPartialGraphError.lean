module

public import RequestProject.Euler.CircularActualCanonicalSectionMatching
public import RequestProject.Euler.CircularBackwardGraphWindowInvariance
public import RequestProject.Euler.CircularFixedGraphQuadraticBound
public import RequestProject.Euler.CircularReferenceUniformTube
public import RequestProject.Euler.BanachExistingReferenceStability

/-! On an arbitrary existing partial block, the actual off-graph
coordinate is controlled by its original off-graph initial error and
its genuine forcing. The comparison curve is the actual unforced flow
on the same already chosen graph. No intermediate projection is
commuted through independent material parameter shifts. -/

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

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  littleCircularReference circularConstrainedTangentSubmodule circularConstrainedChart
  circularConstraintProjectionToTangentCLM circularConstrainedReturnMap circularConstrainedUnstableProjectionCLM
  circularCoRotatedConstrainedMap contourC1GraphSubmodule holderGraphSubmodule

theorem exists_circular_actual_partial_graph_error_constants {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) {R r T : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hT : 0 < T)
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
      ∀ α w : CircularConstrainedTangentSpace γ,
        circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α → ‖α‖ + ‖w‖ ≤ d →
        ∀ {H ε : ℝ}, H ∈ Icc (0 : ℝ) T → 0 ≤ ε →
        ∀ y p : ℝ → Fin 2 → LittleContourSpace γ,
          y 0 = circularConstrainedChart hγ hγ1 (x α 0 + w) →
          (∀ u ∈ Icc (0 : ℝ) H, HasDerivAt y (circularBanachField hγ hγ1 (y u) + p u) u) →
          (∀ u ∈ Icc (0 : ℝ) H, ‖y u - littleCircularMaterialContours hγ hγ1 u‖ ≤ rn) →
          (∀ u ∈ Icc (0 : ℝ) H, ‖p u‖ ≤ ε) →
          ∀ u ∈ Icc (0 : ℝ) H,
            let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1)
            ‖v - x (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) 0‖ ≤ E * (‖w‖ + ε) := by
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  obtain ⟨U, hU, hUD, _, K, rt, hrt, _, _, hLip, htube, _⟩ :=
    exists_circular_reference_uniform_lipschitz_tube hγ hγ1
  obtain ⟨df, hdf, hdfr, Bf, hBf, hflat⟩ :=
    circularFixedBackwardGraph_flattening_lipschitz hγ hγ1 hR hr hX hd hfix harea hg
  obtain ⟨a, ha, Cc, hCc, hchartLip⟩ := exists_circularConstrainedChart_local_lipschitz hγ hγ1
  have hp : 0 < period := by unfold period; positivity
  obtain ⟨S, hS, Y, hY, _, _, _, hareaY, _⟩ :=
    exists_circularContour_constrained_interval_flow hγ hγ1 1 (add_pos hT hp)
  obtain ⟨ν, hν, Cf, hCf, hcoords⟩ := exists_circularCoRotatedFlow_uniform_constraint_coordinates
    hγ hγ1 (add_pos hT hp) hS hrt hY hareaY
  have hw : 1 ≤ circularAncientBackwardWeight := by linarith [circularAncientBackwardWeight_bounds.1]
  obtain ⟨η, hη, hηr, hinv⟩ := exists_same_circularBackwardGraph_window_invariant_radius
    hγ hγ1 hT hR hS hr hw hX (hd.differentiableAt (by norm_num)) hfix harea hY hareaY hg
  let d := min η (min (ν / 4) (min (a / 4) (df / (4 * (‖Q‖ * Cf + 1)))))
  let rn := min rt (df / (‖Q‖ * ‖J‖ + 1))
  let A := (Cc + T + 1) * Real.exp ((K : ℝ) * T)
  let E := Bf * ‖J‖ * A + 1
  have hdpos : 0 < d := lt_min hη (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hrn : 0 < rn := lt_min hrt (by positivity)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨d, hdpos, (min_le_left _ _).trans hηr, rn, hrn, E, hE, ?_⟩
  intro α w hα hsize H ε hH hε y p hinit hyd hnear hforce u hu
  let z := x α 0
  have hαd : ‖α‖ ≤ d := (le_add_of_nonneg_right (norm_nonneg w)).trans hsize
  have hαη : ‖α‖ ≤ η := hαd.trans (min_le_left _ _)
  have hαr : ‖α‖ ≤ r / 2 := hαη.trans hηr
  have hzn : ‖z‖ ≤ 2 * ‖α‖ := by simpa only [pow_zero, mul_one] using hg.norm_le α hα hαr 0
  have hdν : d ≤ ν / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hda : d ≤ a / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdfd : d ≤ df / (4 * (‖Q‖ * Cf + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzν : ‖z‖ < ν := by linarith only [hzn, hαd, hdν, hν]
  have hza : ‖z‖ < a := by linarith only [hzn, hαd, hda, ha]
  have hzwa : ‖z + w‖ < a := by
    have hh := norm_add_le z w
    linarith only [hh, hzn, hsize, hda, norm_nonneg w, ha]
  have hcoord := hcoords z hzν
  let c := fun t : ℝ => Y (circularConstrainedChart hγ hγ1 z) t
  have htime (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : t ∈ Icc (0 : ℝ) (T + period) :=
    ⟨ht.1, by linarith only [ht.2, hH.2, hp]⟩
  have hcm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : c t ∈ U := by
    apply htube t
    apply mem_closedBall.mpr
    rw [dist_eq_norm, ← norm_circularCoRotationCLM_sub_reference hγ hγ1 t]
    exact (mem_ball_iff_norm.mp (hcoord.2 t (htime t ht)).1).le
  have hym (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : y t ∈ U := by
    apply htube t
    exact mem_closedBall.mpr (by
      simpa only [dist_eq_norm] using (hnear t ht).trans (min_le_left _ _))
  have hyc : ContinuousOn y (Icc (0 : ℝ) H) :=
    fun t ht => (hyd t ht).continuousAt.continuousWithinAt
  have hcc : ContinuousOn c (Icc (0 : ℝ) H) :=
    (hY.continuous _ hcoord.1).mono (Icc_subset_Icc_right (by linarith only [hH.2, hp]))
  have hcd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : HasDerivAt c (circularBanachField hγ hγ1 (c t)) t :=
    hY.hasDerivAt _ hcoord.1 t (htime t ht)
  have hi : dist (y 0) (c 0) ≤ Cc * ‖w‖ := by
    rw [hinit, show c 0 = circularConstrainedChart hγ hγ1 z from hY.initial _ hcoord.1]
    simpa only [dist_eq_norm, add_sub_cancel_left] using hchartLip (z + w) z hzwa hza
  have hcompare := dist_existing_forcedCurve_reference_le hε hLip hyc hcc hyd hcd hym hcm hforce hi
  have hcurveError : ‖y u - c u‖ ≤ A * (‖w‖ + ε) := by
    have hh := hcompare u hu
    rw [dist_eq_norm] at hh
    have huT : u ≤ T := hu.2.trans hH.2
    have hscalar : Cc * ‖w‖ + ε * u ≤ (Cc + T + 1) * (‖w‖ + ε) := by
      have hm := mul_le_mul_of_nonneg_left huT hε
      nlinarith only [hm, norm_nonneg w, hε, mul_nonneg hCc.le hε,
        mul_nonneg hT.le (norm_nonneg w)]
    have he : Real.exp ((K : ℝ) * u) ≤ Real.exp ((K : ℝ) * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huT K.coe_nonneg)
    exact hh.trans ((mul_le_mul hscalar he (Real.exp_pos _).le (by positivity)).trans_eq (by
      dsimp only [A]
      ring))
  let v := J (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1)
  let pz := circularCoRotatedConstrainedMap hγ hγ1 Y u z
  have hQv : ‖Q v‖ ≤ df := by
    have hj := J.le_opNorm (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1)
    have hq := Q.le_opNorm v
    rw [norm_circularCoRotationCLM_sub_reference hγ hγ1 u] at hj
    have hh := mul_le_mul_of_nonneg_left (hj.trans
      (mul_le_mul_of_nonneg_left (hnear u hu) (norm_nonneg J))) (norm_nonneg Q)
    have hnr : rn ≤ df / (‖Q‖ * ‖J‖ + 1) := min_le_right _ _
    have hnprod := (le_div_iff₀ (show 0 < ‖Q‖ * ‖J‖ + 1 by positivity)).mp hnr
    nlinarith only [hq, hh, hnprod, hrn.le]
  have hQp : ‖Q pz‖ ≤ df := by
    have hpz : ‖pz‖ ≤ Cf * ‖z‖ := (hcoord.2 u (htime u hu)).2.1
    have hq := Q.le_opNorm pz
    have hsmall := (le_div_iff₀ (show 0 < 4 * (‖Q‖ * Cf + 1) by positivity)).mp hdfd
    have hm := mul_le_mul_of_nonneg_left
      (hpz.trans (mul_le_mul_of_nonneg_left hzn hCf.le)) (norm_nonneg Q)
    have hdcoef := mul_le_mul_of_nonneg_left hαd (show 0 ≤ 2 * ‖Q‖ * Cf by positivity)
    have hprod0 : 0 ≤ ‖Q‖ * Cf * d := by positivity
    nlinarith only [hq, hm, hdcoef, hsmall, hdpos.le, hprod0]
  have hpoint : x (Q pz) 0 = pz := by
    have hi := (hinv u ⟨hu.1, hu.2.trans hH.2⟩ α hα hαη).2
    exact congrFun hi 0
  have hvp : v - pz = J (circularCoRotationCLM γ u (y u - c u)) := by
    have hpzdef : pz = J (circularCoRotationCLM γ u (c u) - littleCircularReference hγ hγ1) := by
      unfold pz circularCoRotatedConstrainedMap circularConstrainedReturnMap
      rfl
    rw [hpzdef]
    change J (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1) -
      J (circularCoRotationCLM γ u (c u) - littleCircularReference hγ hγ1) = _
    simp only [map_sub]
    exact sub_sub_sub_cancel_right _ _ _
  have hcoordError : ‖v - pz‖ ≤ ‖J‖ * A * (‖w‖ + ε) := by
    rw [hvp]
    have hh := J.le_opNorm (circularCoRotationCLM γ u (y u - c u))
    rw [norm_circularCoRotationCLM] at hh
    exact (hh.trans (mul_le_mul_of_nonneg_left hcurveError (norm_nonneg J))).trans_eq (by ring)
  have hf := hflat pz v hQp hQv
  dsimp only at hf
  have hvflat : v - Q v - (x (Q v) 0 - Q v) = v - x (Q v) 0 :=
    sub_sub_sub_cancel_right v (x (Q v) 0) (Q v)
  have hpflat : pz - Q pz - (x (Q pz) 0 - Q pz) = 0 := by rw [hpoint, sub_self]
  change ‖(v - Q v - (x (Q v) 0 - Q v)) - (pz - Q pz - (x (Q pz) 0 - Q pz))‖ ≤
    Bf * ‖v - pz‖ at hf
  rw [hvflat, hpflat, sub_zero] at hf
  change ‖v - x (Q v) 0‖ ≤ E * (‖w‖ + ε)
  apply (hf.trans (mul_le_mul_of_nonneg_left hcoordError hBf.le)).trans
  have hh : Bf * ‖J‖ * A ≤ E := by dsimp only [E]; linarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (add_nonneg (norm_nonneg w) hε)

end Euler2D

end
