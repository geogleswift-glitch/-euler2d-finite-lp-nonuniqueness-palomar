module

public import RequestProject.Euler.BanachExistingReferenceStability
public import RequestProject.Euler.CircularCanonicalHandoffAlignment

/-! Stability on the same original canonical negative-time arc after
one constant exit alignment. All constants precede the actual exit,
angle, forced curve and provisional duration. Future closeness to the
arc is obtained from the real equation by first-exit, not assumed. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6000

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

attribute [local instance 2000] quadraticReferenceC1_group localGraphLittle_group localGraphLittle_space
  localGraphFamily_tower localGraphTangent_group localGraphTangent_space
  localGraphTangent_complete localGraphTangent_continuousAdd

attribute [local irreducible] circularBanachField circularBanachDomain circularCoRotationCLM
  circularCanonicalHandoffAlignmentCLM contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1} (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_canonical_ancient_handoff_stability_constants {s : ℝ} (hs : s < 0) :
    ∃ r > 0, ∃ δ > 0, ∃ η > 0, ∃ K : ℝ≥0,
      ∀ {H ε : ℝ}, 0 ≤ H → H ≤ -s → 0 ≤ ε → ε ≤ η →
      ∀ (exit b : ℝ) (y p : ℝ → Fin 2 → LittleContourSpace γ),
        (∀ u ∈ Icc (0 : ℝ) H, y (exit + u) ∈ circularBanachDomain hγ hγ1) →
        (∀ u ∈ Icc (0 : ℝ) H,
          HasDerivAt y (circularBanachField hγ hγ1 (y (exit + u)) + p (exit + u)) (exit + u)) →
        (∀ u ∈ Icc (0 : ℝ) H, ‖p (exit + u)‖ ≤ ε) →
        ‖circularCoRotationCLM γ exit (y exit) -
          contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s))‖ ≤ δ →
        (∀ u ∈ Icc (0 : ℝ) H,
          ‖circularCanonicalHandoffAlignmentCLM γ s b exit (y (exit + u)) - P.ancient (s + u)‖ < r) ∧
        (∀ u ∈ Icc (0 : ℝ) H,
          ‖circularCanonicalHandoffAlignmentCLM γ s b exit (y (exit + u)) - P.ancient (s + u)‖ ≤
            (‖circularCoRotationCLM γ exit (y exit) -
                contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s))‖ + ε * u) *
              Real.exp ((K : ℝ) * u)) := by
  let c := fun u : ℝ => P.ancient (s + u)
  have htime (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (-s)) : s + u ≤ 0 := by linarith only [hu.2]
  have hcc : ContinuousOn c (Icc (0 : ℝ) (-s)) :=
    P.ancient_continuous.comp (continuous_const.add continuous_id).continuousOn htime
  have hcd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (-s)) :
      HasDerivAt c (circularBanachField hγ hγ1 (c u)) u := by
    have hh := (P.ancient_derivative (s + u) (htime u hu)).scomp u ((hasDerivAt_id u).const_add s)
    simp only [Function.comp_def, one_smul] at hh
    change HasDerivAt (fun v : ℝ => P.ancient (s + v))
      (circularBanachField hγ hγ1 (P.ancient (s + u))) u
    exact hh
  have hcm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) (-s)) : c u ∈ circularBanachDomain hγ hγ1 :=
    (P.ancient_domain (s + u) (htime u hu)).1
  have hdom : IsOpen (circularBanachDomain hγ hγ1) := by
    unfold circularBanachDomain
    exact isOpen_phaseAdmissibleLittleContourFamilies _ _
  have hf : ContDiffOn ℝ 1 (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1) := by
    unfold circularBanachField circularBanachDomain
    exact contDiffOn_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ 1
  obtain ⟨r, hr, δ, hδ, η, hη, K, hstable⟩ :=
    exists_existing_compact_reference_stability_constants hdom hf (neg_pos.mpr hs) hcc hcd hcm
  refine ⟨r, hr, δ, hδ, η, hη, K, ?_⟩
  intro H ε hH hHs hε hεη exit b y p hym hyd hp hinit
  let G := circularCanonicalHandoffAlignmentCLM γ s b exit
  let Y := fun u : ℝ => G (y (exit + u))
  let pY := fun u : ℝ => G (p (exit + u))
  have hYd (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) :
      HasDerivAt Y (circularBanachField hγ hγ1 (Y u) + pY u) u := by
    have hh := (hyd u hu).scomp u ((hasDerivAt_id u).const_add exit)
    have hshift : HasDerivAt (fun v => y (exit + v))
        (circularBanachField hγ hγ1 (y (exit + u)) + p (exit + u)) u := by
      simp only [Function.comp_def, one_smul] at hh
      exact hh
    exact (hasDerivAt_circularCanonicalHandoffAlignment_forced hγ hγ1 s b exit u (hym u hu) hshift).1
  have hYc : ContinuousOn Y (Icc (0 : ℝ) H) :=
    fun u hu => (hYd u hu).continuousAt.continuousWithinAt
  have hpY (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) : ‖pY u‖ ≤ ε := by
    change ‖circularCanonicalHandoffAlignmentCLM γ s b exit (p (exit + u))‖ ≤ ε
    rw [norm_circularCanonicalHandoffAlignmentCLM]
    exact hp u hu
  have hinitEq : dist (Y 0) (c 0) =
      ‖circularCoRotationCLM γ exit (y exit) -
        contourRotationFamilyLittleCLM γ b (circularCoRotationCLM γ s (P.ancient s))‖ := by
    simp only [Y, G, c, add_zero, dist_eq_norm]
    exact circularCanonicalHandoffAlignment_section_error s b exit (y exit) (P.ancient s)
  have hresult := hstable hH hHs hε hεη Y pY hYc hYd hpY (hinitEq.le.trans hinit)
  rw [hinitEq] at hresult
  constructor
  · simpa only [Y, G, c, dist_eq_norm] using hresult.1
  · simpa only [Y, G, c, dist_eq_norm] using hresult.2

end CircularMaterialTransferProfile
end Euler2D

end
