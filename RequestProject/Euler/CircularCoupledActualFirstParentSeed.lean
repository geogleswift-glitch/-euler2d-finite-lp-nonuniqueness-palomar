module

public import RequestProject.Euler.CircularActualFirstParentSeed
public import RequestProject.Euler.CircularCaptureCoupledScaleSmallness

/-! Actual fixed-area unstable seed coordinates on the SAME finite
Euler prefix at R=rho^10, A0=cA*(1+xi). The constraints, chart recovery,
exact growing-coordinate identity and cutoff-uniform seed coefficient
are retained, with the seed coefficient chosen before cA. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance 2000] captureBlockTangent_group captureBlockTangent_space
  captureBlockTangent_continuousAdd captureBlockEndo_monoid captureBlockTangent_complete
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule
  circularConstrainedTangentSubmodule circularConstrainedUnstableProjectionCLM
  circularConstraintProjectionToTangentCLM circularBanachField circularBanachDomain
  finiteBaseCurlL2 CircularMaterialTransferProfile.finiteBaseLp

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_coupled_seed_coordinates
    {b Kw Kcur : ℝ} (hb : 0 < b) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ Cseed > 0, ∀ {s cA q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
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
      ∀ N k : ℕ, ∀ hkN : k ≤ N, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ
        hkN S H Y →
      ∀ t ∈ Icc (0 : ℝ) H, ∀ σ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) 0 σ = t →
      let deviation := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y σ
      weightedFamilyNorm h k deviation ≤ Kw * h → ‖deviation k‖ ≤ Kcur * h →
      let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y σ
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (Z - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) ∧
      (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) ∧
      circularConstrainedChart hγ hγ1 v = Z ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧
      ‖v‖ ≤ Cseed * ρ ^ 6 ∧ ‖α‖ ≤ Cseed * ρ ^ 6 ∧
      ‖α‖ = ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y σ‖ *
        ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ ∧
      ∀ κ : ℝ, 0 < κ →
        κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y σ‖ →
        0 < ‖α‖ ∧ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) * ρ ^ 6 ≤ ‖α‖ := by
  let J := circularConstraintProjectionToTangentCLM hγ hγ1.le
  let Q := circularConstrainedUnstableProjectionCLM hγ hγ1.le
  let Cseed := 2 * (‖Q‖ + 1) * ‖J‖ * Kcur + 1
  have hCseed : 0 < Cseed := by dsimp only [Cseed]; positivity
  obtain ⟨Cgeo, hCgeo, hconstraints⟩ := P.exists_uniform_actualCanonical_prefix_constraints
  obtain ⟨ε, hε, hchart⟩ := exists_circular_actualConstraintChart_radius hγ hγ1
  let δ := min (cellA / 8) (ε / 2)
  have hδ : 0 < δ := lt_min (div_pos cellA_pos (by norm_num)) (half_pos hε)
  have hδquarter : δ ≤ cellA / 4 :=
    (min_le_left _ _).trans (by linarith only [cellA_pos])
  have hδε : δ < ε := (min_le_right _ _).trans_lt (half_lt_self hε)
  have hcore (i : Fin 2) : cellA / 2 ≤ 3 * circularContourRadii i / 4 := by
    have hh := (circularContourRadii_bounds i).2.1
    linarith only [hh, cellA_pos]
  refine ⟨Cseed, hCseed, ?_⟩
  intro s cA q T η _ hs hcA hq hqE hT hη hηa hancient
  let dc := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dc * (1 + ξ)
  have hdRlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dc (1 + dc) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hsmallDR := (hdRlim.eventually (gt_mem_nhds
    (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  have hsmall (A : ℝ) (n : ℕ) (hn : n ≠ 0) (e : ℝ) (he : 0 < e) :
      ∀ᶠ ξ : ℝ in atTop, A * Real.exp (-ξ) ^ n ≤ e := by
    have ht : Tendsto (fun ξ : ℝ => A * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul A
    exact (ht.eventually (gt_mem_nhds he)).mono (fun _ h => h.le)
  filter_upwards [hsmall 1 1 (by decide) (1 / 2) (by norm_num),
    hsmall 1 1 (by decide) (b / 2) (half_pos hb),
    hsmallDR,
    hsmall 2 6 (by decide) 1 (by norm_num),
    hsmall (4 * Kw) 12 (by decide) δ hδ,
    hsmall (2 * Kcur) 6 (by decide) δ hδ, eventually_ge_atTop (0 : ℝ)]
      with ξ hρhalf hρbhalf hdR hh1 hweightedSmall hcurSmall hξ
  simp only [pow_one, one_mul] at hρhalf hρbhalf hdR
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let d := 2 + 4 * Cgeo * A₀ * T
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dc, d, A₀]; ring
  rw [hdeq] at hdR
  have hh : 0 < h := by dsimp only [h]; positivity
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  have hRle : R ≤ ρ := by
    calc
      R = ρ * ρ ^ 9 := by dsimp only [R]; ring
      _ ≤ ρ := mul_le_of_le_one_right hρ.le (pow_le_one₀ hρ.le hρ1)
  have hRhalf : R ≤ 1 / 2 := hRle.trans hρhalf
  have hρb : ρ < b := hρbhalf.trans_lt (half_lt_self hb)
  have hden : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hdiv : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by nlinarith only [hρbhalf])
    linarith only [hdiv]
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
      calc
        _ ≤ Cgeo * A₀ / (1 / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hden
        _ = _ := by ring
    have ht := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [ht, hcat]
  have hweightedSmall' : h * (Kw * h) ≤ δ := by
    have he : h * (Kw * h) = (4 * Kw) * ρ ^ 12 := by dsimp only [h]; ring
    rwa [he]
  have hcurSmall' : Kcur * h ≤ δ := by
    simpa only [h, mul_assoc, mul_left_comm, mul_comm] using hcurSmall
  dsimp only
  intro N k hkN S hS H hH Y hY t ht σ htime hweighted hcur
  have ha := hconstraints (core := cellA / 2) (δ := δ) (C₀ := 2) (K := Kw * h)
    hs hA.le hb hR hRhalf hρ hρ1 hρb hq hqE le_rfl hdrift hdR
    hH hδquarter hcore (by norm_num) hh1 (mul_nonneg hKw hh.le) hweightedSmall'
    hη hηa hancient hkN S hS Y hY t ht 0 σ htime hweighted
    (hcur.trans hcurSmall')
  let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y σ
  let v := J (Z - littleCircularReference hγ hγ1)
  let α := Q v
  have hfour : ∀ i, Z i ∈ fourfoldLittleContourSubmodule γ := by
    intro i
    apply mem_fourfoldLittleContourSubmodule_parameterShift
    have hi := ha.1 i
    rw [canonicalPrefixAlignedCurrentCell_zero_entrance] at hi
    exact hi
  have harea : ∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2 := by
    intro i
    change littleContourArea γ (contourParameterShiftLittleCLM γ _ _) = _
    rw [littleContourArea_parameterShiftLittleCLM]
    have hi := ha.2 i
    rwa [canonicalPrefixAlignedCurrentCell_zero_entrance] at hi
  have hnorm : ‖Z - littleCircularReference hγ hγ1‖ ≤ Kcur * h := by
    rw [norm_canonicalPrefixMaterialCurrent_sub_reference,
      ← canonicalPrefixAlignedCurrentCell_zero_entrance,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference]
    exact hcur
  have hvchart : circularConstrainedChart hγ hγ1 v = Z :=
    hchart Z (mem_ball_iff_norm.mpr ((hnorm.trans hcurSmall').trans_lt hδε)) hfour harea
  have hseed : ‖α‖ = ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y σ‖ *
      ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ :=
    norm_circularConstrainedUnstableProjection_actual_fourfold hγ hγ1 Z hfour
  have hv : ‖v‖ ≤ (2 * ‖J‖ * Kcur) * ρ ^ 6 := by
    calc
      _ ≤ ‖J‖ * ‖Z - littleCircularReference hγ hγ1‖ := J.le_opNorm _
      _ ≤ ‖J‖ * (Kcur * h) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg J)
      _ = _ := by dsimp only [h]; ring
  have hα : ‖α‖ ≤ (2 * ‖Q‖ * ‖J‖ * Kcur) * ρ ^ 6 := by
    calc
      _ ≤ ‖Q‖ * ‖v‖ := Q.le_opNorm _
      _ ≤ ‖Q‖ * ((2 * ‖J‖ * Kcur) * ρ ^ 6) := mul_le_mul_of_nonneg_left hv (norm_nonneg Q)
      _ = _ := by ring
  have hvC : 2 * ‖J‖ * Kcur ≤ Cseed := by
    dsimp only [Cseed]
    nlinarith only [mul_nonneg (norm_nonneg Q) (mul_nonneg (norm_nonneg J) hKcur)]
  have hαC : 2 * ‖Q‖ * ‖J‖ * Kcur ≤ Cseed := by
    dsimp only [Cseed]
    nlinarith only [mul_nonneg (norm_nonneg J) hKcur]
  refine ⟨hfour, harea, hvchart, circularConstrainedUnstableProjectionCLM_idempotent hγ hγ1.le v,
    hv.trans (mul_le_mul_of_nonneg_right hvC (pow_nonneg hρ.le 6)),
    hα.trans (mul_le_mul_of_nonneg_right hαC (pow_nonneg hρ.le 6)), hseed, ?_⟩
  intro κ hκ hlower
  have hemb : 0 < ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ :=
    norm_circularConstrainedUnstableEmbedding_one_pos hγ hγ1.le
  have hbound : (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) * ρ ^ 6 ≤ ‖α‖ := by
    rw [hseed]
    convert mul_le_mul_of_nonneg_right hlower hemb.le using 1 <;> ring
  exact ⟨(mul_pos (mul_pos hκ hemb) (pow_pos hρ 6)).trans_le hbound, hbound⟩

theorem exists_eventually_actualFirstParent_coupled_seed_coordinates
    {b Kw Kcur : ℝ} (hb : 0 < b) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ Cseed > 0, ∀ {s cA q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
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
      ∀ k : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) (k + 1)) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ
        (Nat.le_succ k) S H Y →
      ∀ t ∈ Icc (0 : ℝ) H, ∀ σ : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) 0 σ = t →
      let deviation := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y σ
      weightedFamilyNorm h k deviation ≤ Kw * h → ‖deviation k‖ ≤ Kcur * h →
      let Z := canonicalPrefixMaterialCurrentCell A₀ b R ρ k Y σ
      let v := circularConstraintProjectionToTangentCLM hγ hγ1.le
        (Z - littleCircularReference hγ hγ1)
      let α := circularConstrainedUnstableProjectionCLM hγ hγ1.le v
      (∀ i, Z i ∈ fourfoldLittleContourSubmodule γ) ∧
      (∀ i, littleContourArea γ (Z i) = Real.pi * circularContourRadii i ^ 2) ∧
      circularConstrainedChart hγ hγ1 v = Z ∧
      circularConstrainedUnstableProjectionCLM hγ hγ1.le α = α ∧
      ‖v‖ ≤ Cseed * ρ ^ 6 ∧ ‖α‖ ≤ Cseed * ρ ^ 6 ∧
      ‖α‖ = ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y σ‖ *
        ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖ ∧
      ∀ κ : ℝ, 0 < κ →
        κ * ρ ^ 6 ≤ ‖canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y σ‖ →
        0 < ‖α‖ ∧ (κ * ‖circularConstrainedUnstableEmbeddingCLM hγ hγ1.le 1‖) * ρ ^ 6 ≤ ‖α‖ := by
  obtain ⟨Cseed, hCseed, hseed⟩ := P.exists_eventually_actualFinite_coupled_seed_coordinates hb hKw hKcur
  refine ⟨Cseed, hCseed, ?_⟩
  intro s cA q T η _ hs hcA hq hqE hT hη hηa hancient
  filter_upwards [hseed hs hcA hq hqE hT hη hηa hancient] with ξ hseedξ
  dsimp only
  intro k
  exact hseedξ (k + 1) k (Nat.le_succ k)

end CircularMaterialTransferProfile
end Euler2D

end
