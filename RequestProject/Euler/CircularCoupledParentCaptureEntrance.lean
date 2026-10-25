module

public import RequestProject.Euler.CircularCoupledActualFirstParentSeed
public import RequestProject.Euler.CircularParentCapturePastWindowControls
public import RequestProject.Euler.CircularCoRotatedFlowEndpoints

/-! The actual warmup-end state is the entrance for further capture.
The SAME material prefix and SAME Euler particles give the entire past,
the true ancestor entry, the actual unstable seed and the original chart.
All bounds are uniform in the cutoff and the active prefix. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstraintProjectionToTangentCLM circularBanachField circularBanachDomain
  finiteBaseCurlL2 CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_coupled_parent_capture_entrance
    {b Kw Kcur : ℝ} (hb : 0 < b) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ Cseed > 0, ∀ {s cA q T η δgeom : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → 0 ≤ η → η ≤ cellA / 4 → 0 < δgeom →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := 2 * ρ ^ 6
      ∀ N k : ℕ, ∀ hkN : k ≤ N,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S H Y →
      ∀ entrance D Cpre : ℝ, 0 ≤ entrance → 0 ≤ D → 0 ≤ Cpre →
      entrance + D / ampScale A₀ b k ≤ H →
      (∀ t ∈ Icc (0 : ℝ) entrance,
        let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * t)
        weightedFamilyNorm h k x ≤ h ∧ ‖x k‖ ≤ h) →
      (∀ u ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h) →
      (∀ u ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
      (∀ u ∈ Icc (0 : ℝ) D, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
          Cpre * ρ * radScale R ρ k * (1 + u)) →
      let e := entrance + D / ampScale A₀ b k
      let Cw := Cpre * (1 + D)
      let xE := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e Y
      let yE := canonicalPrefixAlignedCurrentCell A₀ b R ρ k e Y
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (yE 0 - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S e Y ∧
      (∀ t ∈ Icc (0 : ℝ) e, ∃ β : FiniteCircularIndex k → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          δgeom * radScale R ρ p.1) ∧
      (∀ t ∈ Icc (0 : ℝ) e, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ (Cw + 2) * ρ * radScale R ρ k) ∧
      weightedFamilyNorm h k (xE 0) ≤ Kw * h ∧ ‖xE 0 k‖ ≤ Kcur * h ∧
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward e z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) ∧
      canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y (ampScale A₀ b k * e) = yE 0 ∧
      (∀ i, yE 0 i ∈ fourfoldLittleContourSubmodule γ) ∧
      (∀ i, littleContourArea γ (yE 0 i) = Real.pi * circularContourRadii i ^ 2) ∧
      circularConstrainedChart hγ hγ1 v = yE 0 ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧
      ‖v‖ ≤ Cseed * ρ ^ 6 ∧ ‖α‖ ≤ Cseed * ρ ^ 6 ∧
      ‖α‖ = ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
        (ampScale A₀ b k * e)‖ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ ∧
      ∀ κ : ℝ, 0 < κ →
        κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
          (ampScale A₀ b k * e)‖ →
        0 < ‖α‖ ∧ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) * ρ ^ 6 ≤ ‖α‖ := by
  obtain ⟨Cseed, hCseed, hseed⟩ := P.exists_eventually_actualFinite_coupled_seed_coordinates hb hKw hKcur
  refine ⟨Cseed, hCseed, ?_⟩
  intro s cA q T η δgeom _ hs hcA hq hqE hT hη hηa hδgeom hancient
  have hsmall (K : ℝ) (m : ℕ) (hm : m ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, K * Real.exp (-ξ) ^ m ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => K * Real.exp (-ξ) ^ m) atTop (𝓝 0) := by
      simpa only [zero_pow hm, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow m).const_mul K
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  filter_upwards [hseed hs hcA hq hqE hT hη hηa hancient,
    hsmall 2 6 (by decide) 1 (by norm_num),
    hsmall 2 6 (by decide) δgeom hδgeom,
    hsmall (4 * Kw) 12 (by decide) δgeom hδgeom,
    hsmall (2 * Kcur) 6 (by decide) δgeom hδgeom,
    eventually_ge_atTop (0 : ℝ)]
      with ξ hseedξ hh1 hhδ hhKw hcurSmall hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhKw' : h * (Kw * h) ≤ δgeom := by
    convert hhKw using 1 <;> dsimp only [h] <;> ring
  have hcurSmall' : Kcur * h ≤ δgeom := by
    simpa only [h, mul_assoc, mul_left_comm, mul_comm] using hcurSmall
  dsimp only
  intro N k hkN S hS H hH Y hY entrance D Cpre hentrance hD hCpre hEnd
    hpast hweighted hcur hparticlesPast hparticlesWindow
  let e := entrance + D / ampScale A₀ b k
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have he : 0 ≤ e := add_nonneg hentrance (div_nonneg hD hAmp.le)
  have hclockOld : physicalTimeFromNormalized (ampScale A₀ b k) entrance D = e := rfl
  have hclockNew : physicalTimeFromNormalized (ampScale A₀ b k) e 0 = e := by
    simp only [physicalTimeFromNormalized, zero_div, add_zero]
  have hclockOwn : physicalTimeFromNormalized (ampScale A₀ b k) 0
      (ampScale A₀ b k * e) = e := by
    simp only [physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ e hAmp.ne']
  have hown (j : ℕ) (hj : j ≤ k) :
      canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * e) j =
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y D j :=
    canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ le_rfl Y Y
      e entrance D 0 (ampScale A₀ b k * e) hclockOld hclockOwn (fun _ => rfl) j hj
  have hnew (j : ℕ) (hj : j ≤ k) :
      canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e Y 0 j =
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y D j :=
    canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ le_rfl Y Y
      e entrance D e 0 hclockOld hclockNew (fun _ => rfl) j hj
  have hweightedOwn : weightedFamilyNorm h k
      (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * e)) ≤ Kw * h := by
    rw [weightedFamilyNorm_congr_prefix h k (fun j => hown j j.isLt.le)]
    exact hweighted D ⟨hD, le_rfl⟩
  have hcurOwn : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y
      (ampScale A₀ b k * e) k‖ ≤ Kcur * h := by
    rw [hown k le_rfl]
    exact hcur D ⟨hD, le_rfl⟩
  have hweightedEntry : weightedFamilyNorm h k
      (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e Y 0) ≤ Kw * h := by
    rw [weightedFamilyNorm_congr_prefix h k (fun j => hnew j j.isLt.le)]
    exact hweighted D ⟨hD, le_rfl⟩
  have hcurEntry : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k e Y 0 k‖ ≤ Kcur * h := by
    rw [hnew k le_rfl]
    exact hcur D ⟨hD, le_rfl⟩
  have hgeometry := canonicalPrefix_material_tube_of_past_and_window hγ hγ1 hA hb hR hρ
    hentrance hD hh hh1 hKw hhδ hhKw' hcurSmall' k Y hpast hweighted hcur
  have hparticles := actual_particles_past_and_window_radius S
    (P.finiteInnerActiveInitialLabels s A₀ b R ρ N k) hA hb hR hρ hentrance hD hCpre k
    hparticlesPast hparticlesWindow
  have hcell : canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y (ampScale A₀ b k * e) =
      canonicalPrefixAlignedCurrentCell A₀ b R ρ k e Y 0 := by
    have hhcell := canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hb.ne' R ρ k e 0 Y
    simpa only [add_zero, circularCoRotationCLM_zero] using hhcell
  have hdata := hseedξ N k hkN S hS hH Y hY e ⟨he, hEnd⟩
    (ampScale A₀ b k * e) hclockOwn hweightedOwn hcurOwn
  dsimp only at hdata
  rw [hcell] at hdata
  exact ⟨hY.mono hEnd, hgeometry, hparticles.1, hweightedEntry, hcurEntry, hparticles.2, hcell, hdata⟩

end CircularMaterialTransferProfile
end Euler2D

end
