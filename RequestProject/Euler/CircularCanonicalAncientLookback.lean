module

public import RequestProject.Euler.CircularCanonicalAncientHandoffStability
public import RequestProject.Euler.CircularCanonicalHandoffEntry

/-! Fixed-length backward stability along the ORIGINAL ancient arc.
The same constant physical/material handoff frame is valid at the
earlier entry. Closeness on the lookback segment is derived by the
proved compact-reference first-exit theorem, never assumed. -/

@[expose] public section

set_option maxHeartbeats 22000000
set_option maxRecDepth 7000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

theorem circularCanonicalHandoffAlignment_shift_both {γ : ℝ≥0}
    (s angle exit u : ℝ) (Y : Fin 2 → LittleContourSpace γ) :
    circularCanonicalHandoffAlignmentCLM γ (s - u) angle (exit - u) Y =
      circularCanonicalHandoffAlignmentCLM γ s angle exit Y := by
  funext i
  apply littleContour_eq_of_lift_eq
  intro θ
  rw [lift_circularCanonicalHandoffAlignment, lift_circularCanonicalHandoffAlignment]
  congr 2
  ring

theorem circularCanonicalHandoffAlignment_shifted_section_error {γ : ℝ≥0}
    (s angle exit u : ℝ) (Y A : Fin 2 → LittleContourSpace γ) :
    ‖circularCoRotationCLM γ (exit - u) Y -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ (s - u) A)‖ =
      ‖circularCanonicalHandoffAlignmentCLM γ s angle exit Y - A‖ := by
  rw [← circularCanonicalHandoffAlignment_section_error (s - u) angle (exit - u) Y A,
    circularCanonicalHandoffAlignment_shift_both]

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  circularCanonicalHandoffAlignmentCLM contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_canonical_ancient_lookback_stability_constants {s L : ℝ}
    (hs : s ≤ 0) (hL : 0 < L) :
    ∃ r > 0, ∃ δ > 0, ∃ η > 0, ∃ K : ℝ≥0,
      ∀ {H ε : ℝ}, 0 ≤ H → H ≤ L → 0 ≤ ε → ε ≤ η →
      ∀ (exit angle : ℝ) (y p : ℝ → Fin 2 → LittleContourSpace γ),
        (∀ u ∈ Icc (0 : ℝ) H, y (exit - u) ∈ circularBanachDomain hγ hγ1) →
        (∀ u ∈ Icc (0 : ℝ) H,
          HasDerivAt y (circularBanachField hγ hγ1 (y (exit - u)) + p (exit - u)) (exit - u)) →
        (∀ u ∈ Icc (0 : ℝ) H, ‖p (exit - u)‖ ≤ ε) →
        ‖circularCoRotationCLM γ exit (y exit) -
          contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ s (P.ancient s))‖ ≤ δ →
        (∀ u ∈ Icc (0 : ℝ) H,
          ‖circularCanonicalHandoffAlignmentCLM γ s angle exit (y (exit - u)) - P.ancient (s - u)‖ < r) ∧
        (∀ u ∈ Icc (0 : ℝ) H,
          ‖circularCanonicalHandoffAlignmentCLM γ s angle exit (y (exit - u)) - P.ancient (s - u)‖ ≤
            (‖circularCoRotationCLM γ exit (y exit) -
                contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ s (P.ancient s))‖ + ε * u) *
              Real.exp ((K : ℝ) * u)) := by
  let c := fun u : ℝ => P.ancient (s - u)
  have htime (u : ℝ) (hu : u ∈ Icc (0 : ℝ) L) : s - u ≤ 0 := by linarith only [hs, hu.1]
  have hcc : ContinuousOn c (Icc (0 : ℝ) L) :=
    P.ancient_continuous.comp (continuous_const.sub continuous_id).continuousOn htime
  have hcd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) L) :
      HasDerivAt c (-circularBanachField hγ hγ1 (c u)) u := by
    have hp : HasDerivAt (fun v : ℝ => s - v) (-1) u := by
      simpa only [zero_sub] using (hasDerivAt_const u s).sub (hasDerivAt_id u)
    have hh := (P.ancient_derivative (s - u) (htime u hu)).scomp u hp
    simpa only [neg_one_smul] using hh
  have hcm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) L) : c u ∈ circularBanachDomain hγ hγ1 :=
    (P.ancient_domain (s - u) (htime u hu)).1
  have hdom : IsOpen (circularBanachDomain hγ hγ1) := by
    unfold circularBanachDomain
    exact isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 (fun Z => -circularBanachField hγ hγ1 Z) (circularBanachDomain hγ hγ1) := by
    have hh : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) := by
      unfold circularBanachField circularBanachDomain
      exact contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1
    exact hh.neg
  obtain ⟨r, hr, δ, hδ, η, hη, K, hstable⟩ :=
    exists_existing_compact_reference_stability_constants hdom hf hL hcc hcd hcm
  refine ⟨r, hr, δ, hδ, η, hη, K, ?_⟩
  intro H ε hH hHL hε hεη exit angle y p hym hyd hp hinit
  let G := circularCanonicalHandoffAlignmentCLM γ s angle exit
  let Y := fun u : ℝ => G (y (exit - u))
  let pY := fun u : ℝ => -(G (p (exit - u)))
  have hYd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) :
      HasDerivAt Y (-circularBanachField hγ hγ1 (Y u) + pY u) u := by
    have hparam : HasDerivAt (fun v : ℝ => exit - v) (-1) u := by
      simpa only [zero_sub] using (hasDerivAt_const u exit).sub (hasDerivAt_id u)
    have hh := (hasDerivAt_circularCanonicalHandoffAlignment_forced hγ hγ1 s angle exit
      (exit - u) (hym u hu) (hyd u hu)).1
    simpa only [neg_one_smul, neg_add] using hh.scomp u hparam
  have hYc : ContinuousOn Y (Icc (0 : ℝ) H) :=
    fun u hu => (hYd u hu).continuousAt.continuousWithinAt
  have hpY (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) : ‖pY u‖ ≤ ε := by
    change ‖-circularCanonicalHandoffAlignmentCLM γ s angle exit (p (exit - u))‖ ≤ ε
    rw [norm_neg, norm_circularCanonicalHandoffAlignmentCLM]
    exact hp u hu
  have hinitEq : dist (Y 0) (c 0) =
      ‖circularCoRotationCLM γ exit (y exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ s (P.ancient s))‖ := by
    simp only [Y, G, c, sub_zero, dist_eq_norm]
    exact circularCanonicalHandoffAlignment_section_error s angle exit (y exit) (P.ancient s)
  have hresult := hstable hH hHL hε hεη Y pY hYc hYd hpY (hinitEq.le.trans hinit)
  rw [hinitEq] at hresult
  constructor
  · simpa only [Y, G, c, dist_eq_norm] using hresult.1
  · simpa only [Y, G, c, dist_eq_norm] using hresult.2

theorem exists_canonical_ancient_lookback_entry_accuracy {s L ζ : ℝ}
    (hs : s ≤ 0) (hL : 0 < L) (hζ : 0 < ζ) :
    ∃ δ > 0, ∃ ε > 0,
      ∀ (exit angle : ℝ) (y p : ℝ → Fin 2 → LittleContourSpace γ),
        (∀ u ∈ Icc (0 : ℝ) L, y (exit - u) ∈ circularBanachDomain hγ hγ1) →
        (∀ u ∈ Icc (0 : ℝ) L,
          HasDerivAt y (circularBanachField hγ hγ1 (y (exit - u)) + p (exit - u)) (exit - u)) →
        (∀ u ∈ Icc (0 : ℝ) L, ‖p (exit - u)‖ ≤ ε) →
        ‖circularCoRotationCLM γ exit (y exit) -
          contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ s (P.ancient s))‖ ≤ δ →
        ‖circularCoRotationCLM γ (exit - L) (y (exit - L)) -
          contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ (s - L) (P.ancient (s - L)))‖ < ζ := by
  obtain ⟨r, hr, δ₀, hδ₀, η, hη, K, hstable⟩ :=
    P.exists_canonical_ancient_lookback_stability_constants hs hL
  let M := Real.exp ((K : ℝ) * L)
  let δ := min δ₀ (ζ / (4 * M))
  let ε := min η (δ / L)
  have hM : 0 < M := Real.exp_pos _
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hε : 0 < ε := lt_min hη (div_pos hδ hL)
  have hεL : ε * L ≤ δ := (le_div_iff₀ hL).mp (min_le_right _ _)
  have hδM : δ * M ≤ ζ / 4 := by
    apply (le_div_iff₀ hM).mp
    calc
      _ ≤ ζ / (4 * M) := min_le_right _ _
      _ = (ζ / 4) / M := by ring
  refine ⟨δ, hδ, ε, hε, ?_⟩
  intro exit angle y p hym hyd hp hinit
  have hh := (hstable hL.le le_rfl hε.le (min_le_left _ _) exit angle y p hym hyd hp
    (hinit.trans (min_le_left _ _))).2 L ⟨hL.le, le_rfl⟩
  rw [circularCanonicalHandoffAlignment_shifted_section_error s angle exit L (y (exit - L))
    (P.ancient (s - L))]
  have hb : (‖circularCoRotationCLM γ exit (y exit) - contourRotationFamilyLittleCLM γ angle
      (circularCoRotationCLM γ s (P.ancient s))‖ + ε * L) * M ≤ (δ + δ) * M :=
    mul_le_mul_of_nonneg_right (add_le_add hinit hεL) hM.le
  exact (hh.trans hb).trans_lt (by nlinarith only [hδM, hζ])

end CircularMaterialTransferProfile
end Euler2D

end
