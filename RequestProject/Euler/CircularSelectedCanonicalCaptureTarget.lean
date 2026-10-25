module

public import RequestProject.Euler.CircularCanonicalCaptureSectionMatching

/-! One selected original canonical target is retained as proved data. Actual later sections are matched to that SAME target on the SAME Euler trajectory. -/

@[expose] public section

set_option maxHeartbeats 24000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule circularCoRotationCLM
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def IsSelectedCanonicalCaptureTarget
    (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
    (δ sCanon ε Ctarget : ℝ) : Prop :=
  sCanon < 0 ∧ 0 < δ ∧ 0 < ε ∧ 0 < Ctarget ∧
    ‖P.coRotatedAncientGraphBase sCanon‖ = δ ∧
    ∀ Z ∈ ball (littleCircularReference hγ hγ1) ε,
      (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) →
      (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) →
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (Z - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      ‖α‖ = δ → ∃ angle : ℝ,
        circularConstrainedChart hγ hγ1 (gseq α 0) =
          contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sCanon (P.ancient sCanon)) ∧
        ‖Z - contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Ctarget * ‖v - gseq α 0‖

theorem exists_uniform_actualCanonical_capture_matches_selected_target :
    ∃ Cgeo > 0,
      ∀ (gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ)
        (δ sCanon ε Ctarget : ℝ),
      P.IsSelectedCanonicalCaptureTarget gseq δ sCanon ε Ctarget →
      ∀ {s A₀ b R ρ q T Hglob a dglob Dphys entrance Dcap core δgeom η C₀ K error : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < dglob → dglob * R ≤ 1 / 4 →
      0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap →
      δgeom ≤ cellA / 4 → δgeom < ε → (∀ i, core ≤ 3 * circularContourRadii i / 4) →
      0 < C₀ → C₀ * ρ ^ 6 ≤ 1 → 0 ≤ K → C₀ * ρ ^ 6 * K ≤ δgeom →
      0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ {N k : ℕ} (hkN : k ≤ N),
      entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (C₀ * ρ ^ 6) k (x τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ δgeom) →
      HasFirstCircularCoRotatedCaptureSection hγ hγ1 y Dcap δ →
      (∀ τ ∈ Icc (0 : ℝ) Dcap,
        let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
          (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1)
        ‖v - gseq (circularConstrainedUnstableProjectionCLM hγ hγ1.le v) 0‖ ≤ error) →
      ∃ τ ∈ Ioc (0 : ℝ) Dcap,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Ioc entrance Dphys ∧
        ∃ angle : ℝ,
          ‖circularCoRotationCLM γ τ (y τ) - contourRotationFamilyLittleCLM γ angle
            (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Ctarget * error ∧
          ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
            (circularConstraintProjectionToTangentCLM hγ hγ1.le
              (circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1))‖ = δ ∧
          ∀ u ∈ Ico (0 : ℝ) τ,
            ‖circularConstrainedUnstableProjectionCLM hγ hγ1.le
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (circularCoRotationCLM γ u (y u) - littleCircularReference hγ hγ1))‖ < δ := by
  obtain ⟨Cgeo, hCgeo, hconstraints⟩ := P.exists_uniform_actualCanonical_prefix_constraints
  refine ⟨Cgeo, hCgeo, ?_⟩
  intro gseq δ sCanon ε Ctarget htarget
  obtain ⟨hsCanon, hδ, hε, hCtarget, hsδ, hpointMatch⟩ := htarget
  intro s A₀ b R ρ q T Hglob a dglob Dphys entrance Dcap core δgeom η C₀ K error _
    hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys he hDcap
    hδgeom hnear hcore hC₀ hh1 hK hhK hη hηa hancient N k hkN htimeEnd S hS X hX
  dsimp only
  let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
  intro hZ hcur hfirst hoff
  obtain ⟨τ, hτ, hvalue, hbefore⟩ := hfirst
  have hτcc : τ ∈ Icc (0 : ℝ) Dcap := ⟨hτ.1.le, hτ.2⟩
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance τ
  have ht : t ∈ Icc (0 : ℝ) Dphys :=
    ⟨add_nonneg he (div_nonneg hτ.1.le hAk.le),
      (add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)).trans htimeEnd⟩
  obtain ⟨hfour, hareaY⟩ := hconstraints hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE
    hglobT hdrift hdR hDphys hδgeom hcore hC₀ hh1 hK hhK hη hηa hancient hkN
    S hS X hX t ht entrance τ rfl (hZ τ hτcc) (hcur τ hτcc)
  let Z := circularCoRotationCLM γ τ (y τ)
  have hZnear : Z ∈ ball (littleCircularReference hγ hγ1) ε := by
    apply mem_ball_iff_norm.mpr
    change ‖circularCoRotationCLM γ τ (y τ) - littleCircularReference hγ hγ1‖ < ε
    rw [norm_circularCoRotationCLM_sub_reference hγ hγ1,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
    exact (hcur τ hτcc).trans_lt hnear
  have hfourZ := circularCoRotationCLM_fourfold τ (y τ) hfour
  have hareaZ (i : Fin 2) : littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2 :=
    (circularCoRotationCLM_area τ (y τ) i).trans (hareaY i)
  obtain ⟨angle, hcanonical, hmatch⟩ := hpointMatch Z hZnear hfourZ hareaZ hvalue
  refine ⟨τ, hτ, ⟨lt_add_of_pos_right entrance (div_pos hτ.1 hAk), ht.2⟩,
    angle, hmatch.trans (mul_le_mul_of_nonneg_left (hoff τ hτcc) hCtarget.le), hvalue, hbefore⟩

end CircularMaterialTransferProfile
end Euler2D

end
