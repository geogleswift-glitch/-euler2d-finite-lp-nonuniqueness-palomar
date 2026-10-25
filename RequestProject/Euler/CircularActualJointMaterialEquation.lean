module

public import RequestProject.Euler.CircularFirstTransferFamily
public import RequestProject.Euler.CircularActualMaterialForcedEquation

/-! The complete real material equation from actual joint contour and
particle controls. No material tube, source support or analytic contour
bounds are supplied independently of the same original trajectory. -/

@[expose] public section

set_option maxHeartbeats 40000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

theorem circularMaterialCurrent_bounds_of_small_error {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (Z : Fin 2 → LittleContourSpace γ)
    (hsmall : ‖Z - littleCircularReference hγ hγ1‖ ≤ 1)
    (hcore : ‖Z - littleCircularReference hγ hγ1‖ ≤ cellA / 4) :
    (∀ i z, ‖ContourC1Space.toBCF γ (Z i).val z‖ ≤ ‖littleCircularReference hγ hγ1‖ + 2) ∧
    (∀ i z, cellA / 2 ≤ ‖ContourC1Space.toBCF γ (Z i).val z‖) ∧
    ∀ i, ‖Z i‖ ≤ ‖littleCircularReference hγ hγ1‖ + 1 := by
  have hnorm : ‖Z‖ ≤ ‖littleCircularReference hγ hγ1‖ + 1 := by
    calc
      _ = ‖(Z - littleCircularReference hγ hγ1) + littleCircularReference hγ hγ1‖ := by
        congr 1
        abel
      _ ≤ ‖Z - littleCircularReference hγ hγ1‖ + ‖littleCircularReference hγ hγ1‖ := norm_add_le _ _
      _ ≤ _ := by linarith only [hsmall]
  refine ⟨?_, ?_, ?_⟩
  · intro i z
    change ‖LittleContourSpace.eval γ z (Z i)‖ ≤ _
    exact ((LittleContourSpace.norm_eval_le _ _).trans
      ((norm_le_pi_norm Z i).trans hnorm)).trans (by linarith)
  · intro i z
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hdiff : ‖LittleContourSpace.lift γ (Z i) θ - refCircle (circularContourRadii i) θ‖ ≤ cellA / 4 := by
      change ‖LittleContourSpace.eval γ (θ : ContourCircle)
        ((Z - littleCircularReference hγ hγ1) i)‖ ≤ _
      exact (LittleContourSpace.norm_eval_le _ _).trans
        ((norm_le_pi_norm (Z - littleCircularReference hγ hγ1) i).trans hcore)
    have hn := norm_sub_norm_le (refCircle (circularContourRadii i) θ) (LittleContourSpace.lift γ (Z i) θ)
    rw [norm_refCircle_actual, abs_of_pos (circularContourRadii_bounds i).1, norm_sub_rev] at hn
    have hr := (circularContourRadii_bounds i).2.1
    change cellA / 2 ≤ ‖LittleContourSpace.lift γ (Z i) θ‖
    linarith only [hn, hdiff, hr, cellA_pos]
  · intro i
    exact (norm_le_pi_norm Z i).trans hnorm

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actual_firstParent_source_support_of_particle_radius
    {s A₀ b R ρ Cb D t : ℝ} (k : ℕ)
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T)
    (ha1 : Cb * ρ * radScale R ρ k * (1 + D) < 1)
    (hparticles : ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k,
      ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale R ρ k * (1 + D)) :
    (∀ y ∈ torusBox, Cb * ρ * radScale R ρ k * (1 + D) < ‖y - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ (k + 1) k S t y = 0) ∧
    (∀ z, Cb * radScale R ρ (k + 1) * (1 + D) < ‖z‖ →
      boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) (k + 1)) t) z = 0) ∧
    ∀ z, Cb * radScale R ρ (k + 1) * (1 + D) < ‖z‖ →
      P.finiteInnerClusterComplexSource s A₀ b R ρ (k + 1) (k + 1) S t z = 0 := by
  let a := Cb * ρ * radScale R ρ k * (1 + D)
  have hlabels (j : ℕ) (hj : j ∈ Finset.Ico (k + 1) ((k + 1) + 1)) :
      ∀ y ∈ torusBox, a < ‖y - torusCenter‖ →
        S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) j) t y = 0 := by
    apply S.transportedScalar_support_of_particle_radius
      (A := P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k) ht ha1
      (fun z hz => hz.1) _ hparticles
    intro z hz hnot
    by_contra hne
    exact hnot ⟨hz, j, hj, hne⟩
  have hscale : Cb * radScale R ρ (k + 1) * (1 + D) = a := by
    dsimp only [a, radScale]
    rw [pow_succ]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro y hy hfar
    exact Finset.sum_eq_zero (fun j hj => hlabels j hj y hy hfar)
  · intro z hz
    rw [hscale] at hz
    exact boxedComplexDensity_support
      (hlabels (k + 1) (by simp only [Finset.mem_Ico]; omega)) z hz
  · intro z hz
    simp [finiteInnerClusterComplexSource, finiteInnerClusterSource, boxedComplexDensity]

theorem exists_eventually_actualFirstParent_material_forced_equation
    {b Cb Kw Kcur : ℝ} (hb : 0 < b) (hb1 : b ≤ 1)
    (hCb : 0 ≤ Cb) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ C > 0,
      ∀ {s A₀ q T D : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hA : 0 < A₀) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → 0 ≤ D → ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let h := 2 * ρ ^ 6
        ∀ k : ℕ,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) (k + 1)) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ (Nat.le_succ k) S H Y →
        ∀ t ∈ Icc (0 : ℝ) H, ∀ σ₀ τ θc : ℝ,
        let σ := σ₀ + b * τ
        physicalTimeFromNormalized (ampScale A₀ b k) 0 σ = t →
        let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y σ
        weightedFamilyNorm h k x ≤ Kw * h → ‖x k‖ ≤ Kcur * h →
        (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ (k + 1) k,
          ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale ρ ρ k * (1 + D)) →
        ∀ η : ℝ, 0 ≤ η → ∀ M : ℂ,
        (‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ (k + 1) (k + 1)) t)) 4 -
          (ampScale A₀ b (k + 1) : ℂ) * (radScale ρ ρ (k + 1) : ℂ) ^ 6 *
            Complex.exp (-(4 * (θc : ℂ) * I)) * M‖ ≤
          ampScale A₀ b (k + 1) * radScale ρ ρ (k + 1) ^ 6 * η) →
        ∃ E : ℂ, ‖E‖ ≤ C * (ρ ^ 8 * (1 + D) ^ 8 + ρ ^ 6 * η) ∧
          HasDerivAt
            (fun u => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b ρ ρ k Y (σ₀ + b * u))
            ((b : ℂ) * lamStar * canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b ρ ρ k Y σ +
              (ρ : ℂ) ^ 6 * Kstar * Complex.exp
                (4 * (((t * finiteAncestorAngularVelocity A₀ b k - θc : ℝ) : ℂ)) * I) * M + E) τ := by
  let L := ‖littleCircularReference hγ hγ1‖ + 1
  let B := ‖littleCircularReference hγ hγ1‖ + 2
  let core := cellA / 2
  let δtube := cellA / 8
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hcore : 0 < core := half_pos cellA_pos
  have hδtube : 0 < δtube := div_pos cellA_pos (by norm_num)
  have hδquarter : δtube ≤ cellA / 4 := by dsimp only [δtube]; linarith only [cellA_pos]
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  obtain ⟨Cforce, hCforce, r, hr, hforce⟩ :=
    P.exists_uniform_actualCanonical_material_forced_equation hb hb1 hcore hB hL hCb
      (by norm_num : (1 : ℝ) ≤ 2) hKw hKcur
  obtain ⟨Cgeo, hCgeo, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  let rcap := min r (min 1 δtube)
  have hrcap : 0 < rcap := lt_min hr (lt_min (by norm_num) hδtube)
  refine ⟨Cforce, hCforce, ?_⟩
  intro s A₀ q T D _ hs hA hq hqE hT hD
  let d := 2 + 4 * Cgeo * A₀ * T
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hsmall (A : ℝ) (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, A * Real.exp (-ξ) ^ n ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => A * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul A
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  filter_upwards [hsmall 1 1 (by decide) (1 / 2) (by norm_num),
    hsmall 1 1 (by decide) (b / 2) (half_pos hb),
    hsmall 1 2 (by decide) (b / 2) (half_pos hb),
    hsmall (5 / 4) 1 (by decide) cellA cellA_pos,
    hsmall (5 / 4) 1 (by decide) (1 / 16) (by norm_num),
    hsmall 2 6 (by decide) 1 (by norm_num),
    hsmall (4 * Kw) 12 (by decide) δtube hδtube,
    hsmall (2 * Kcur) 6 (by decide) rcap hrcap,
    hsmall 2 8 (by decide) (1 / 2) (by norm_num),
    hsmall (8 * B) 1 (by decide) core hcore,
    hsmall d 1 (by decide) (1 / 4) (by norm_num),
    hsmall (L + 1) 1 (by decide) (1 / 32) (by norm_num),
    hsmall (Cb * (1 + D)) 2 (by decide) (1 / 16) (by norm_num),
    hsmall (8 * Cb * (1 + D)) 1 (by decide) core hcore]
      with ξ hρhalf hρbhalf hρsq hρcore hρchart hh1 hweightedSmall hcurSmall hζ hsepB hdR hgeom hchart hsep
  simp only [pow_one, one_mul] at hρhalf hρbhalf hρsq hρcore hρchart hsepB hdR hgeom hsep
  let ρ := Real.exp (-ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  have hρb : ρ < b := hρbhalf.trans_lt (half_lt_self hb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hdiv : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by nlinarith only [hρbhalf])
    linarith only [hdiv]
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have ht := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [ht, hcat]
  have hweightedSmall' : h * (Kw * h) ≤ δtube := by
    have heq : h * (Kw * h) = (4 * Kw) * ρ ^ 12 := by dsimp only [h]; ring
    rw [heq]
    exact hweightedSmall
  have hcurSmall' : Kcur * h ≤ rcap := by
    simpa only [h, mul_assoc, mul_comm, mul_left_comm] using hcurSmall
  have hcurTube : Kcur * h ≤ δtube :=
    hcurSmall'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcurOne : Kcur * h ≤ 1 :=
    hcurSmall'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcurR : Kcur * h ≤ r := hcurSmall'.trans (min_le_left _ _)
  dsimp only
  intro k S hS H hH Y hY t ht σ₀ τ θc htime hweighted hcur hparticles η hη M hclose
  let σ := σ₀ + b * τ
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y σ
  let Z := canonicalPrefixAbsoluteFamily A₀ b ρ ρ k 0 Y σ
  let u : ℕ → ℝ := fun l => ampScale A₀ b l * 0 + b ^ (k - l) * σ
  let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
  have hcurTube' : ‖x k‖ ≤ δtube := hcur.trans hcurTube
  obtain ⟨G, hG, hqrow⟩ := hgeo (core := core) (δ := δtube) (C₀ := 2) (K := Kw * h)
    hs hA.le hb hρ hρhalf hρ hρ1 hρb hq hqE le_rfl hdrift hdR hH
    (Nat.le_succ k) S hS Y hY t ht hδquarter hcorei (by norm_num) hh1
    (mul_nonneg hKw hh.le) hweightedSmall' Z u φ hweighted hcurTube' (by
      intro p
      have heq := congrArg (fun W : Fin 2 → LittleContourSpace γ => (W p.2).val)
        (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hρ hρ k 0 σ Y p.1)
      rw [htime] at heq
      simpa only [Z, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
        Pi.smul_apply] using heq.symm)
  have hnormEq : ‖canonicalPrefixAbsoluteCell A₀ b ρ ρ k 0 Y σ (Fin.last k) -
      littleCircularMaterialContours hγ hγ1 σ‖ = ‖x k‖ := by
    rw [← canonicalPrefixAlignedCurrentCell_zero_entrance,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference]
  have hfine : ‖canonicalPrefixAbsoluteCell A₀ b ρ ρ k 0 Y σ (Fin.last k) -
      littleCircularMaterialContours hγ hγ1 σ‖ ≤ Kcur * h := by
    rw [hnormEq]
    exact hcur
  have hmatfine : ‖canonicalPrefixMaterialCurrentCell A₀ b ρ ρ k Y σ -
      littleCircularReference hγ hγ1‖ ≤ Kcur * h := by
    rw [norm_canonicalPrefixMaterialCurrent_sub_reference]
    exact hfine
  have hbounds := circularMaterialCurrent_bounds_of_small_error hγ hγ1
    (canonicalPrefixMaterialCurrentCell A₀ b ρ ρ k Y σ)
    (hmatfine.trans hcurOne) ((hmatfine.trans hcurTube).trans hδquarter)
  have hrad : radScale ρ ρ k ≤ ρ :=
    mul_le_of_le_one_right hρ.le (pow_le_one₀ hρ.le hρ1)
  have hgeomK : (L + 1) * radScale ρ ρ k ≤ (1 / 16 : ℝ) / 2 := by
    calc
      _ ≤ (L + 1) * ρ := mul_le_mul_of_nonneg_left hrad (by linarith only [hL])
      _ ≤ 1 / 32 := hgeom
      _ = _ := by norm_num
  have ha : Cb * ρ * radScale ρ ρ k * (1 + D) ≤ 1 / 16 := by
    calc
      _ ≤ Cb * ρ * ρ * (1 + D) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (mul_nonneg hCb hρ.le)) (by linarith only [hD])
      _ = (Cb * (1 + D)) * ρ ^ 2 := by ring
      _ ≤ _ := hchart
  have ha1 : Cb * ρ * radScale ρ ρ k * (1 + D) < 1 := ha.trans_lt (by norm_num)
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, (hY.mem t ht).1.2⟩
  obtain ⟨hsupport, hchild, hdeep⟩ := P.actual_firstParent_source_support_of_particle_radius k S htT ha1 hparticles
  have hwf : P.finiteInitialPeriodicDensity s A₀ b ρ ρ (k + 1) =ᵐ[μT]
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) (k + 1) : R2 → ℝ) := by
    filter_upwards [P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hρ hρ hq hqE (k + 1),
      ae_restrict_mem measurableSet_torusBox] with z hz hzbox
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hρ hρhalf hρ hρ1 (k + 1) hzbox).trans hz.symm
  exact hforce (s := s) (A₀ := A₀) (R := ρ) (ρ := ρ) (a := 1 / 16) (δ := δtube)
    (D := D) (η := η) (Hglob := T) (H := H)
    hs hA hρ hρhalf le_rfl hρ hρ1 hρsq (by norm_num) le_rfl hD hη hζ hsepB hρchart hρcore
    (k + 1) k (Nat.le_succ k) le_rfl S hS le_rfl hwf Y hY t ht G hG x
    hweighted hcur hqrow hgeomK ha ha1 hsupport hchild hdeep
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hsep) σ₀ τ θc htime
    (hfine.trans hcurR) hfine hbounds.1 hbounds.2.1 hbounds.2.2 M hclose

end CircularMaterialTransferProfile
end Euler2D

end
