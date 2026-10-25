module

public import RequestProject.Euler.CircularActualFirstParentSeed
public import RequestProject.Euler.CircularFirstTransferLateChoice
public import RequestProject.Euler.CircularFiniteEulerUniformVectorCorrection

/-! A true first-parent equation with a polynomial forcing coefficient
chosen BEFORE the observation window. Particle confinement is derived
anew on the same Euler system, so this coefficient does not inherit
the window-dependent constants of its preliminary O(rho^6) bounds. -/

@[expose] public section

set_option maxHeartbeats 48000000
set_option maxRecDepth 9500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] circularBanachField circularBanachDomain

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFirstParent_preCapture_forcing
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    ∃ Cb > 0, ∃ Bpoly > 0, ∃ Ktorus > 0, ∃ εchart > 0,
      ∀ {D Kw Kcur s A₀ q T η : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hA : 0 < A₀) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ D → 0 ≤ Kw → 0 ≤ Kcur → 0 ≤ T → 0 ≤ η → η ≤ cellA / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let h := 2 * ρ ^ 6
      ∀ k : ℕ, ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) (k + 1)) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ
        (Nat.le_succ k) S H Y →
      ∀ entrance : ℝ, 0 ≤ entrance → entrance + D / ampScale A₀ b k ≤ H →
      (∀ u ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y u) ≤ Kw * h) →
      (∀ u ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y u k‖ ≤ Kcur * h) →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ (k + 1) k,
        ‖S.forward entrance z - torusCenter‖ ≤ 2 * ρ * radScale ρ ρ k) →
      let y := canonicalPrefixAlignedCurrentCell A₀ b ρ ρ k entrance Y
      ∃ p : ℝ → Fin 2 → LittleContourSpace γ,
        (∀ u ∈ Icc (0 : ℝ) D,
          HasDerivAt y (circularBanachField hγ hγ1 (y u) + p u) u ∧
          ‖p u‖ ≤ Ktorus * ρ ^ 8 * ‖y u - littleCircularMaterialContours hγ hγ1 u‖ +
            Bpoly * ρ ^ 6 * (1 + u) ^ 4 ∧
          y u ∈ circularBanachDomain hγ hγ1 ∧
          (y u ∈ ball (littleCircularReference hγ hγ1) εchart →
            circularConstrainedChart hγ hγ1
              (circularConstraintProjectionToTangentCLM hγ hγ1.le
                (y u - littleCircularReference hγ hγ1)) = y u)) ∧
        ∀ u ∈ Icc (0 : ℝ) D, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ (k + 1) k,
          ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance u) z - torusCenter‖ ≤
            Cb * ρ * radScale ρ ρ k * (1 + u) := by
  obtain ⟨Cp, Cr, Kr, hCp, hCr, hKr, hparticles⟩ :=
    P.exists_uniform_actualCanonical_inner_particle_confinement hb hb1 (by norm_num : (0 : ℝ) ≤ 2)
  obtain ⟨Cdyn, Ct, Cd, εchart, hCdyn, hCt, hCd, hεchart, hdynamics⟩ :=
    P.exists_uniform_actualCanonical_alignedCurrent_dynamics
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let δ := cellA / 8
  let Cb := radialStageRadiusConstant Cr 2 b
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let Ktorus := Ct * torusRow + 1
  let Bpoly := finiteCurrentPolynomialForcingCoefficient (γ : ℝ) (cellA / 2) L Cb b Cd + 1
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let Cgeo := max Cp Cdyn
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have hδ : 0 < δ := div_pos cellA_pos (by norm_num)
  have hδa : δ ≤ cellA / 4 := by dsimp only [δ]; linarith only [cellA_pos]
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr (by norm_num) hb hb1
  have htorusRow : 0 ≤ torusRow := finiteTorusLabelLittleRowCoefficient_nonneg hL.le
  have hKtorus : 0 < Ktorus := by dsimp only [Ktorus]; positivity
  have hBpoly : 0 < Bpoly := by
    dsimp only [Bpoly]
    have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
      (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
        (half_pos cellA_pos) 0).trans (le_max_left _ _)
    have htor : 0 ≤ torusCorrectionContourBudget (γ : ℝ) L := by
      unfold torusCorrectionContourBudget
      positivity
    unfold finiteCurrentPolynomialForcingCoefficient
    positivity [finiteLabelMassBound_nonneg]
  have hCgeo : 0 < Cgeo := hCp.trans_le (le_max_left _ _)
  refine ⟨Cb, hCb, Bpoly, hBpoly, Ktorus, hKtorus, εchart, hεchart, ?_⟩
  intro D Kw Kcur s A₀ q T η _ hs hA hq hqE hD hKw hKcur hT hη hηa hancient
  let d := 2 + 4 * Cgeo * A₀ * T
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hd : 0 < d := by dsimp only [d]; nlinarith only [hcat]
  have hsmall (A : ℝ) (n : ℕ) (hn : n ≠ 0) (e : ℝ) (he : 0 < e) :
      ∀ᶠ ξ : ℝ in atTop, A * Real.exp (-ξ) ^ n ≤ e := by
    have ht : Tendsto (fun ξ : ℝ => A * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul A
    exact (ht.eventually (gt_mem_nhds he)).mono (fun _ h => h.le)
  have he2 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 2) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.pow 2
  have he8 : Tendsto (fun ξ : ℝ => Real.exp (-ξ) ^ 8) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.pow 8
  have hdenLim : Tendsto (fun ξ : ℝ => 1 - b * Real.exp (-ξ) ^ 2) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub (he2.const_mul b)
  let radialLimit := (32 / (15 * core ^ 4) * circularRadialPerturbationWeight) * δ
  have hradial : Tendsto (fun ξ : ℝ => finiteEulerUniformRadialCoefficient Kr b
      (Real.exp (-ξ)) (Real.exp (-ξ)) core d δ) atTop (𝓝 radialLimit) := by
    have hfirst := (tendsto_const_nhds : Tendsto (fun _ : ℝ => radialLimit) atTop
      (𝓝 radialLimit)).div hdenLim (by norm_num : (1 : ℝ) ≠ 0)
    have hsecond := ((tendsto_circularFiniteL1Coefficient_exp_neg b).const_mul (Kr * d ^ 4)).mul he8
    simpa only [finiteEulerUniformRadialCoefficient, div_one, mul_zero, add_zero] using hfirst.add hsecond
  have hcubic : ∀ᶠ ξ : ℝ in atTop,
      b * finiteEulerUniformRadialCoefficient Kr b (Real.exp (-ξ)) (Real.exp (-ξ)) core d δ *
        Cb ^ 3 * Real.exp (-ξ) ^ 2 * (1 + D) ^ 3 ≤ Cr / 2 := by
    have ht : Tendsto (fun ξ : ℝ => b * finiteEulerUniformRadialCoefficient Kr b
        (Real.exp (-ξ)) (Real.exp (-ξ)) core d δ * Cb ^ 3 * Real.exp (-ξ) ^ 2 * (1 + D) ^ 3)
        atTop (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using
        (((hradial.const_mul b).mul_const (Cb ^ 3)).mul he2).mul_const ((1 + D) ^ 3)
    exact (ht.eventually (gt_mem_nhds (half_pos hCr))).mono (fun _ h => h.le)
  filter_upwards [hcubic,
    hsmall 1 1 (by decide) (1 / 2) (by norm_num),
    hsmall 1 1 (by decide) (b / 2) (half_pos hb),
    hsmall 1 2 (by decide) (b / 2) (half_pos hb),
    hsmall (5 / 4) 1 (by decide) cellA cellA_pos,
    hsmall (5 / 4) 1 (by decide) (1 / 16) (by norm_num),
    hsmall d 1 (by decide) (1 / 16) (by norm_num),
    hsmall 2 6 (by decide) 1 (by norm_num),
    hsmall (4 * Kw) 12 (by decide) δ hδ,
    hsmall (2 * Kcur) 6 (by decide) δ hδ,
    hsmall 2 8 (by decide) (1 / 2) (by norm_num),
    hsmall (8 * L) 1 (by decide) core hcore,
    hsmall (8 * b * Kw * (Cl + Ct * torusRow)) 8 (by decide) 1 (by norm_num),
    hsmall (Cb * (1 + D)) 1 (by decide) (core / 2) (half_pos hcore),
    hsmall (Cb * (1 + D)) 1 (by decide) d hd,
    hsmall (Cb * (1 + D)) 2 (by decide) (1 / 16) (by norm_num),
    hsmall (8 * Cb * (1 + D)) 1 (by decide) core hcore,
    hsmall (L + 1) 1 (by decide) (1 / 32) (by norm_num)]
      with ξ hcubicξ hρhalf hρbhalf hρsq hρcore hρchart hdR hh1 hweightedSmall hcurSmall
        hζ hsepL houter hinnerCore hinnerChart hchart hsep hgeom
  simp only [pow_one, one_mul] at hρhalf hρbhalf hρsq hρcore hρchart hdR
  simp only [pow_one, one_mul] at hsepL hinnerCore hinnerChart hsep hgeom
  let ρ := Real.exp (-ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hh : 0 < h := by dsimp only [h]; positivity
  have hρ1 : ρ ≤ 1 := hρhalf.trans (by norm_num)
  have hρb : ρ < b := hρbhalf.trans_lt (half_lt_self hb)
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hdiv : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by nlinarith only [hρbhalf])
    linarith only [hdiv]
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
      calc
        _ ≤ Cgeo * A₀ / (1 / 2) :=
          div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
        _ = _ := by ring
    have ht := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [ht, hcat]
  have hdriftFor (C : ℝ) (hC : C ≤ Cgeo) :
      5 / 4 + (C * A₀ / (1 - ρ / b)) * T < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA.le) hden.le) hT)).trans_lt hdrift
  have hweightedSmall' : h * (Kw * h) ≤ δ := by
    have he : h * (Kw * h) = (4 * Kw) * ρ ^ 12 := by dsimp only [h]; ring
    rwa [he]
  have hcurSmall' : Kcur * h ≤ δ := by
    simpa only [h, mul_assoc, mul_left_comm, mul_comm] using hcurSmall
  have houter' : (2 * b * 2 * (Kw * h) * (Cl + Ct * torusRow)) * ρ ^ 2 ≤ 1 := by
    convert houter using 1 <;> dsimp only [h] <;> ring
  dsimp only
  intro k S hS H hH Y hY entrance hentrance htimeEnd hZ hcur hstart
  have hcurTube (u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) :
      ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y u k‖ ≤ δ :=
    (hcur u hu).trans hcurSmall'
  have hparticle := hparticles (c := core) (δ := δ) (C₀ := 2) (K := Kw * h)
    hs hA hρ hρhalf hρ hρ1 hρbhalf hq hqE le_rfl
    (hdriftFor Cp (le_max_left _ _)) hdR hcore hd hH hentrance hD hρsq hδa hcorei
    (by norm_num) (mul_nonneg hKw hh.le) hh1 hweightedSmall' hcubicξ
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hinnerCore)
    (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hinnerChart)
    (k + 1) k (Nat.le_succ k) htimeEnd S hS Y hY hZ hcurTube hstart
  have hrad : radScale ρ ρ k ≤ ρ :=
    mul_le_of_le_one_right hρ.le (pow_le_one₀ hρ.le hρ1)
  have hgeomK : (L + 1) * radScale ρ ρ k ≤ (1 / 16 : ℝ) / 2 := by
    calc
      _ ≤ (L + 1) * ρ := mul_le_mul_of_nonneg_left hrad (by positivity)
      _ ≤ 1 / 32 := hgeom
      _ = _ := by norm_num
  have hchartK : Cb * ρ * radScale ρ ρ k * (1 + D) ≤ 1 / 16 := by
    calc
      _ ≤ Cb * ρ * ρ * (1 + D) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrad (mul_nonneg hCb.le hρ.le))
          (by linarith only [hD])
      _ = (Cb * (1 + D)) * ρ ^ 2 := by ring
      _ ≤ _ := hchart
  obtain ⟨p, hp⟩ := hdynamics (c := core) (δ := δ) (C₀ := 2) (K := Kw * h)
    (Δ := 1) hs hA hb hb1.le hρ hρhalf hρ hρ1 hρb hq hqE le_rfl
    (hdriftFor Cdyn (le_max_right _ _)) (hdR.trans (by norm_num)) hH hentrance hD
    (le_refl (0 : ℝ)) hρsq hρcore (by norm_num) (by norm_num) hcore hcorei hδa
    hη hηa hancient hCb.le (by norm_num) (mul_nonneg hKw hh.le) (by norm_num)
    hh1 hweightedSmall' hζ hsepL hρchart houter' (k + 1) k (Nat.le_succ k)
    htimeEnd hgeomK (by simpa only [add_zero, zero_add] using hchartK)
    (by simpa only [add_zero, zero_add, core, mul_assoc, mul_left_comm, mul_comm] using hsep)
    S hS Y hY hZ hcurTube
    (by simpa only [add_zero, zero_add] using hparticle)
  refine ⟨p, ?_, hparticle⟩
  intro u hu
  have hpu := hp u hu
  refine ⟨hpu.1, ?_, hpu.2.2.1, hpu.2.2.2⟩
  have hcoef : Ct * torusRow ≤ Ktorus := by dsimp only [Ktorus]; linarith
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hρ.le 8))
    (norm_nonneg (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ k entrance Y u -
      littleCircularMaterialContours hγ hγ1 u))
  have hraw : ‖p u‖ ≤ Ct * torusRow * ρ ^ 8 *
      ‖canonicalPrefixAlignedCurrentCell A₀ b ρ ρ k entrance Y u -
        littleCircularMaterialContours hγ hγ1 u‖ + Bpoly * ρ ^ 6 * (1 + u) ^ 4 := by
    simpa only [add_zero, zero_add, Bpoly, torusRow] using hpu.2.1
  exact hraw.trans (add_le_add hterm le_rfl)

end CircularMaterialTransferProfile
end Euler2D

end
