module

public import RequestProject.Euler.CircularCoupledFirstParentCaptureCone
public import RequestProject.Euler.CircularCoupledCanonicalNonzeroParentWindow

/-! The real arbitrary-cutoff parent produced by the nonzero-window
construction has a genuine graph-cone entrance after a long warmup.
The improved particle coefficient is chosen BEFORE that warmup length,
so its later capture forcing budget has no circular duration choice. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option maxRecDepth 10000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal ContDiff BigOperators

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockTangent_space captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstrainedReturnMap circularConstrainedChart circularConstraintProjectionToTangentCLM
  circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualCanonical_coupled_capture_ready {Rflow r₀ : ℝ}
    (hRflow : 0 < Rflow) (hr₀ : 0 < r₀)
    {Xflow : (Fin 2 → LittleContourSpace γ) → ℝ → Fin 2 → LittleContourSpace γ}
    (hflow : IsBanachFlowOn (circularBanachField hγ hγ1) (circularBanachDomain hγ hγ1)
      (ball (littleCircularReference hγ hγ1) Rflow) period Xflow)
    (hd : ContDiffAt ℝ 2 (fun W => Xflow W period) (littleCircularReference hγ hγ1))
    (hfix : Xflow (littleCircularReference hγ hγ1) period = littleCircularReference hγ hγ1)
    (harea : ∀ W ∈ ball (littleCircularReference hγ hγ1) Rflow, ∀ i,
      littleContourArea γ (Xflow W period i) = littleContourArea γ (W i))
    {gseq : CircularConstrainedTangentSpace γ → ℕ → CircularConstrainedTangentSpace γ}
    (hg : IsLocalWeightedBackwardGraph
      (banachDoubleReturn (circularConstrainedReturnMap hγ hγ1 (fun W => Xflow W period)))
      (circularConstrainedUnstableProjectionCLM hγ hγ1.le) circularAncientBackwardWeight r₀ gseq)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ∃ qc : ℝ, 1 < qc ∧
      qc ^ 2 < circularCaptureBlockMultiplier ℓ ∧ ∃ Ccomp > 0, ∃ Cpre > 0,
      ∀ nWarm : ℕ, ∀ {Kw Kcur κ : ℝ}, 0 ≤ Kw → 0 ≤ Kcur → 0 < κ →
      Ccomp * qc ^ nWarm ≤ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32 →
      ∀ {s cA q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        let D := (nWarm : ℝ) * circularCaptureBlockTime ℓ
        ∀ N k : ℕ, ∀ hkN : k ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S H Y →
        ∀ entrance : ℝ, 0 ≤ entrance → entrance + D / ampScale A₀ b k ≤ H →
        (∀ u ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u) ≤ Kw * h) →
        (∀ u ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u k‖ ≤ Kcur * h) →
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y 0 k‖ ≤ h →
        (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward entrance z - torusCenter‖ ≤ 2 * ρ * radScale R ρ k) →
        κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y
          (ampScale A₀ b k * entrance + D)‖ →
        let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y (ampScale A₀ b k * entrance + D)
        let v := circularConstraintProjectionToTangentCLM hγ hγ1.le (Z - littleCircularReference hγ hγ1)
        let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
        0 < ‖α‖ ∧ ‖v - gseq α 0‖ ≤ ‖α‖ / 32 ∧ circularConstrainedChart hγ hγ1 v = Z ∧
          ∀ u ∈ Icc (0 : ℝ) D, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
            ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
              Cpre * ρ * radScale R ρ k * (1 + u) := by
  obtain ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, hcomplement⟩ :=
    P.exists_eventually_actualFinite_coupled_preCapture_complement hRflow hr₀ hflow hd hfix harea hg hb hb1
  obtain ⟨Cpre, hCpre, Bpoly, hBpoly, Ktorus, hKtorus, εchart, hεchart, hforcing⟩ :=
    P.exists_eventually_actualFinite_coupled_preCapture_forcing hb hb1
  refine ⟨ℓ, hℓ, qc, hqc, hgap, Ccomp, hCcomp, Cpre, hCpre, ?_⟩
  intro nWarm Kw Kcur κ hKw hKcur hκ hbudget s cA q T η _ hs hcA hq hqE hT hη hηa hancient
  let D := (nWarm : ℝ) * circularCaptureBlockTime ℓ
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (circularCaptureBlockTime_pos hℓ).le
  obtain ⟨Cseed, hCseed, hseed⟩ := P.exists_eventually_actualFinite_coupled_seed_coordinates hb hKw hKcur
  filter_upwards [hseed hs hcA hq hqE hT hη hηa hancient,
    hcomplement nWarm hs hcA hq hqE hKw hKcur hT hη hηa hancient,
    hforcing (D := D) hs hcA hq hqE hD hKw hKcur hT hη hηa hancient,
    eventually_ge_atTop (0 : ℝ)] with ξ hseedξ hcompξ hforceξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro N k hkN S hS H hH Y hY entrance hentrance hEnd hweighted hcur hinit hstart hlower
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  let σend := ampScale A₀ b k * entrance + D
  let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y σend
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let v := J (Z - littleCircularReference hγ hγ1)
  let α := Q v
  have hclock (u : ℝ) : physicalTimeFromNormalized (ampScale A₀ b k) 0
      (ampScale A₀ b k * entrance + u) = physicalTimeFromNormalized (ampScale A₀ b k) entrance u := by
    unfold physicalTimeFromNormalized
    field_simp [hAmp.ne'] <;> ring
  have hown (u : ℝ) (j : ℕ) (hj : j ≤ k) :
      canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (ampScale A₀ b k * entrance + u) j =
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y u j :=
    canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.ne' R ρ le_rfl Y Y
      (physicalTimeFromNormalized (ampScale A₀ b k) entrance u)
      entrance u 0 (ampScale A₀ b k * entrance + u) rfl (hclock u) (fun _ => rfl) j hj
  have hownWeighted : weightedFamilyNorm h k
      (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y σend) ≤ Kw * h := by
    rw [weightedFamilyNorm_congr_prefix h k (fun j => hown D j j.isLt.le)]
    exact hweighted D ⟨hD, le_rfl⟩
  have hownCur : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y σend k‖ ≤ Kcur * h := by
    rw [hown D k le_rfl]
    exact hcur D ⟨hD, le_rfl⟩
  have htime : entrance + D / ampScale A₀ b k ∈ Icc (0 : ℝ) H :=
    ⟨add_nonneg hentrance (div_nonneg hD hAmp.le), hEnd⟩
  obtain ⟨hfourZ, hareaZ, hchart, hαrange, hvNorm, hαNorm, hcoordinate, hSeedLower⟩ :=
    hseedξ N k hkN S hS hH Y hY (entrance + D / ampScale A₀ b k) htime σend (hclock D)
      hownWeighted hownCur
  obtain ⟨hαpos, hαlower⟩ := hSeedLower κ hκ hlower
  have hcompAll := hcompξ N k hkN S hS hH Y hY entrance hentrance hEnd hweighted hcur hinit hstart
  have hcompEnd := hcompAll nWarm le_rfl
  have hZgrid : Z = canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance Y
      ((nWarm : ℝ) * circularCaptureBlockTime ℓ) := by
    dsimp only [Z, σend]
    rw [canonicalPrefixMaterialCurrentCell_eq_coRotatedAligned hA.ne' hb.ne' R ρ k entrance D Y,
      circularCoRotationCLM_capture_grid]
  have hcompZ : ‖v - gseq α 0‖ ≤ Ccomp * qc ^ nWarm * ρ ^ 6 := by
    dsimp only [v, α]
    rw [hZgrid]
    exact hcompEnd
  have hcone : ‖v - gseq α 0‖ ≤ ‖α‖ / 32 := by
    calc
      _ ≤ Ccomp * qc ^ nWarm * ρ ^ 6 := hcompZ
      _ ≤ ((κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) / 32) * ρ ^ 6 :=
        mul_le_mul_of_nonneg_right hbudget (pow_nonneg hρ.le 6)
      _ = ((κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) * ρ ^ 6) / 32 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hαlower (by norm_num)
  obtain ⟨p, hp, hpure⟩ := hforceξ N k hkN S hS hH Y hY entrance hentrance hEnd hweighted hcur hstart
  exact ⟨hαpos, hcone, hchart, hpure⟩

end CircularMaterialTransferProfile
end Euler2D

end
