module

public import RequestProject.Euler.CircularCoupledFirstParentWindow

/-! Construct the next actual parent prefix on the SAME finite Euler
system at arbitrary depth. The full child past and real inner-particle
fence are retained; the future parent trajectory is a CONCLUSION.
No assumption that the deeper transported cluster is empty is used. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 64000000
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

theorem exists_actualCoupledCanonical_parent_window_setup :
    ∃ Kself : ℝ≥0, 0 < Kself ∧
      ∀ b : ℝ≥0, 0 < b → b < 1 / 4 →
      (b : ℝ) * Kself + (b : ℝ) *
        (finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2)
          (circularCanonicalCellNormBudget hγ hγ1) / (2 - 1)) < sigma / 4 →
      ∀ {Dobs η : ℝ},
      0 < Dobs → 0 < η → η ≤ cellA / 16 → η ≤ (1 - cellA) / 16 →
      ∃ Cb > 0, ∃ Ccur > 0, ∃ Cobs > 0,
      ∀ {s cA q T : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < T → (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let R := ρ ^ 10
        let hR := pow_pos hρ 10
        let A₀ := cA * (1 + ξ)
        let h := 2 * ρ ^ 6
        ∀ N k : ℕ, ∀ hk : 0 < k, ∀ hkN : k ≤ N,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR hρ) N) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ entrance : ℝ, 0 < entrance →
        entrance + (b : ℝ) * Dobs / ampScale A₀ b (k - 1) < T →
        ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ hkN S entrance X →
        (∀ u ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance),
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X u) ≤ 1) →
        (∀ u ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance),
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X u k‖ ≤ η) →
        (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
          ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k) →
        ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
          P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ
            ((Nat.sub_le k 1).trans hkN) S
              (entrance + (b : ℝ) * Dobs / ampScale A₀ b (k - 1)) Y ∧
          (∀ u ∈ Icc (0 : ℝ) ((b : ℝ) * Dobs),
            weightedFamilyNorm h (k - 1)
              (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y u) ≤ Cobs * h) ∧
          (∀ u ∈ Icc (0 : ℝ) ((b : ℝ) * Dobs),
            ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y u (k - 1)‖ ≤ Ccur * h) ∧
          (∀ u ∈ Icc (0 : ℝ) ((b : ℝ) * Dobs), ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
            ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b (k - 1)) entrance u) z - torusCenter‖ ≤
              Cb * ρ * radScale R ρ (k - 1) * (1 + u)) ∧
          (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
            ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ (k - 1)) ∧
          ∀ t ∈ Icc (0 : ℝ) entrance,
            let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) 0 Y
              (ampScale A₀ b (k - 1) * t)
            weightedFamilyNorm h (k - 1) x ≤ h ∧ ‖x (k - 1)‖ ≤ h ∧
              (2 ≤ k → ‖x (k - 2)‖ ≤ h ^ 2) := by
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw, hwindowAll⟩ :=
    P.exists_uniform_actual_parent_observation_window
  obtain ⟨Creset, hCreset, hreset⟩ := P.exists_uniform_actualCanonical_crossPrefix_weighted_reset
  obtain ⟨Cmaterial, hCmaterial, hmaterial⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  refine ⟨Kself, hKself, ?_⟩
  intro b hb hbquarter hslow Dobs η hDobs hη hηa hηgap
  have hbR : 0 < (b : ℝ) := hb
  have hb1 : b < 1 := hbquarter.trans (by norm_num)
  let L := circularCanonicalCellNormBudget hγ hγ1
  let core := cellA / 2
  let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
  let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) core L L
  let torusRow := finiteTorusLabelLittleRowCoefficient (γ : ℝ) L
  let Dparent := (b : ℝ) * Dobs
  have hDparent : 0 < Dparent := mul_pos hbR hDobs
  obtain ⟨CgeoWin, Ctc, Cdc, Cr, Kr, Ccur, Cobs, hCgeoWin, hCtc, hCdc, hCr, hKr, hCcur, hCobs,
    hwindow⟩ := hwindowAll b hb hb1 (D := Dparent) (C₀ := 2) (K := 1) (νbar := sigma / 3)
      hDparent (by norm_num) (by norm_num) hη hηa hηgap
  let Cb := radialStageRadiusConstant Cr 2 b
  let Cgeo := CgeoWin + Creset + Cmaterial + 1
  have hL : 0 < L := circularCanonicalCellNormBudget_pos hγ hγ1
  have hcore : 0 < core := half_pos cellA_pos
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  have hCgeo : 0 < Cgeo := by dsimp only [Cgeo]; positivity
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr (by norm_num) hbR hb1
  have hcauchy : 0 ≤ cauchyContourNormBudget 5 (γ : ℝ) 1 (cellA / 2) L :=
    (cauchySpatialDerivativeBudget_nonneg 5 (by norm_num : (0 : ℝ) ≤ 1)
      (half_pos cellA_pos) 0).trans (le_max_left _ _)
  have hinterior : 0 ≤ interiorContourNormBudget (γ : ℝ) 1 core L L :=
    (interiorSpatialDerivativeBudget_nonneg (M := 1) (a := core) (by norm_num) hL 0).trans
      (le_max_left _ _)
  have hweight : 0 ≤ circularRadialPerturbationWeight :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (circularContourRadii_bounds i).1.le)
  have hCu : 0 ≤ Cu := by unfold Cu finiteInnerLabelLittleRowCoefficient; positivity
  have hCl : 0 ≤ Cl := by unfold Cl finiteOuterLabelLittleRowCoefficient; positivity
  have htorusRow : 0 ≤ torusRow := finiteTorusLabelLittleRowCoefficient_nonneg hL.le
  refine ⟨Cb, hCb, Ccur, hCcur, Cobs, hCobs, ?_⟩
  intro s cA q T _ hs hcA hq hqE hT hancient
  let p : DeepestCaptureScaleData :=
    { b := b, L := L, core := core, rw := rw, Kboot := 2,
      δgeom := η, δcur := η, Cb := Cb, Cr := Cr, Kr := Kr, d := 0,
      Cgeo := Cgeo, A₀ := cA, T := T, torusW := Ctw * torusRow,
      torusC := Ctc * torusRow, Cl := Cl, C := 0, E := 0, lam := 2,
      Damp := 0, κ₀ := 1, ε₀ := 1, Bpoly := 0, F := 0, seed := 1,
      referenceNorm := ‖littleCircularReference hγ hγ1‖, q := 2,
      Ncap := 1, blockTime := Dparent }
  have hp : p.CoupledAdmissible :=
    ⟨hbR, hcore, hrw, hη, hCr, hcA, hCgeo.le, hT.le,
      (by norm_num [p]), (by norm_num [p]), (by norm_num [p]), (by norm_num [p])⟩
  have hrate := eventually_circularCapture_selected_ratio_gap
    (K := (Kself : ℝ)) (C₀ := 2) (Ctorus := 3 * Ctw * torusRow)
    hbR hCu hCl (by norm_num) (by positivity) hslow
  have hsmall (C : ℝ) (n : ℕ) (hn : n ≠ 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ ξ : ℝ in atTop, C * Real.exp (-ξ) ^ n ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => C * Real.exp (-ξ) ^ n) atTop (𝓝 0) := by
      simpa only [zero_pow hn, mul_zero] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.pow n).const_mul C
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  filter_upwards [hwindow, p.eventually_coupled_budget hp, hrate,
    hsmall 1 1 (by decide) (cellA / 256) (div_pos cellA_pos (by norm_num)),
    hsmall 2 6 (by decide) η hη,
    hsmall (max 2 (Cb * (1 + Dparent))) 1 (by decide)
      (cellA / 128) (div_pos cellA_pos (by norm_num))]
    with ξ hwindowξ hbudget hrateξ hρsmall hhη hbuffer
  simp only [pow_one, one_mul] at hρsmall hbuffer
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let d := 2 + 4 * Cgeo * A₀ * T
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := hbudget.amplitude_pos
  have hd : 0 < d := hbudget.support_pos
  have hcat : 0 < Cgeo * A₀ * T := mul_pos (mul_pos hCgeo hA) hT
  have hh : 0 < h := by dsimp only [h]; positivity
  have hρhalf : ρ ≤ 1 / 2 := hbudget.half
  have hρ1 : ρ ≤ 1 := hbudget.one
  have hρbhalf : ρ ≤ (b : ℝ) / 2 := hbudget.bhalf
  have hρsq : ρ ^ 2 ≤ (b : ℝ) / 2 := hbudget.sq_bhalf
  have hρcore : (5 / 4 : ℝ) * ρ ≤ cellA := hbudget.initial_core
  have hsepU : 10 * ρ ≤ core := hbudget.upper_sep
  have hsepL : 8 * L * ρ ≤ core := hbudget.lower_sep
  have hh1 : 2 * ρ ^ 6 ≤ 1 := hbudget.weight
  have hhboot : (2 * ρ ^ 6) * 2 ≤ min rw η := hbudget.weighted_bootstrap
  have hζ : 2 * ρ ^ 8 ≤ 1 / 2 := hbudget.row
  have hRρ : R ≤ ρ := hbudget.scale_le
  have hRhalf : R ≤ 1 / 2 := hRρ.trans hρhalf
  have hCtRw : Ctw * torusRow * R ^ 8 ≤ 1 := hbudget.torus
  have hdR : d * R ≤ 1 / 16 := hbudget.radius
  have hgeom : (L + 1) * R ≤ 1 / 32 := hbudget.geometry
  have houter : (2 * (b : ℝ) * 2 * 2 * (Cl + Ctc * torusRow)) * ρ ^ 2 ≤ 1 := hbudget.outer_source
  have hcubicξ : (b : ℝ) * finiteEulerUniformRadialCoefficient Kr b R ρ core d η *
      Cb ^ 3 * ρ ^ 2 * (1 + Dparent) ^ 3 ≤ Cr / 2 := by
    simpa only [p, DeepestCaptureScaleData.duration, Nat.cast_one, one_mul,
      DeepestCaptureScaleData.coupledSupport, DeepestCaptureScaleData.coupledAmplitude,
      d, A₀, R, ρ, deepestCaptureScale] using hbudget.radial
  have hinnerCore : Cb * ρ * (1 + Dparent) ≤ core / 2 := by
    simpa only [p, DeepestCaptureScaleData.duration, Nat.cast_one, one_mul] using hbudget.particle_core
  have hinnerChart : Cb * ρ * (1 + Dparent) ≤ d := by
    simpa only [p, DeepestCaptureScaleData.duration, Nat.cast_one, one_mul,
      DeepestCaptureScaleData.coupledSupport, DeepestCaptureScaleData.coupledAmplitude,
      d, A₀, ρ, deepestCaptureScale] using hbudget.particle_outer
  have hchart : Cb * ρ * R * (1 + Dparent) ≤ 1 / 16 := by
    simpa only [p, DeepestCaptureScaleData.duration, Nat.cast_one, one_mul] using hbudget.particle_box
  have hsep : 8 * (Cb * ρ * (1 + Dparent)) ≤ core := by
    simpa only [p, DeepestCaptureScaleData.duration, Nat.cast_one, one_mul] using hbudget.particle_sep
  have hρb : ρ < (b : ℝ) := hρbhalf.trans_lt (half_lt_self hbR)
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh' : ρ / b ≤ 1 / 2 := (div_le_iff₀ hbR).mpr (by nlinarith only [hρbhalf])
    linarith only [hh']
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hm := mul_le_mul_of_nonneg_right hdiv hT.le
    dsimp only [d]
    nlinarith only [hm, hcat]
  have hdriftFor (C : ℝ) (hC : C ≤ Cgeo) : 5 / 4 + (C * A₀ / (1 - ρ / b)) * T < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA.le) hden.le) hT.le)).trans_lt hdrift
  have hWinC : CgeoWin ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCreset, hCmaterial]
  have hResetC : Creset ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCgeoWin, hCmaterial]
  have hMaterialC : Cmaterial ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCgeoWin, hCreset]
  have hβ : 0 ≤ 3 * (Ctw * torusRow * R ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ := by
    have hfb := weightedInteractionRowFeedback_nonneg hbR.le hCu hCl (by norm_num)
      (hζ.trans_lt (by norm_num))
    positivity
  have hν : ((b * Kself : ℝ≥0) : ℝ) +
      (3 * (Ctw * torusRow * R ^ 8) + weightedInteractionRowFeedback b Cu Cl 2 ρ) ≤ sigma / 3 := by
    simpa only [weightedNormPropagationExponent, NNReal.coe_mul, mul_assoc, add_assoc] using ((hrateξ.2 R hR.le hRρ).2)
  have hηquarter : η ≤ cellA / 4 := by linarith only [hηa, cellA_pos]
  have hdRquarter : d * R ≤ 1 / 4 := hdR.trans (by norm_num)
  have hρchartStrict : (5 / 4 : ℝ) * R < 1 / 16 := hbudget.initial_chart
  have hsizeStrict : R * (‖littleCircularReference hγ hγ1‖ + η) < (1 / 16 : ℝ) / 4 := by
    convert hbudget.domain using 1 <;> norm_num
  have hbufferStrict : max 2 (Cb * (1 + Dparent)) * ρ < cellA / 64 :=
    hbuffer.trans_lt (by nlinarith only [cellA_pos])
  dsimp only
  intro N k hk hkN S hS entrance hentrance htarget X hX hweighted hcur hdeeper
  have hAmp (j : ℕ) : 0 < ampScale A₀ b j := div_pos hA (pow_pos hbR j)
  let Hparent := entrance + Dparent / ampScale A₀ b (k - 1)
  have hwindow' := hwindowξ (s := s) (A₀ := A₀) (R := R) (q := q) (T := T)
    (Hglob := T) (a := 1 / 16) (d := d) (entrance := entrance)
    hs hA hR hq hqE hRhalf hRρ hρ1 hρbhalf hρsmall hρsq hρcore hsepU hsepL
    hh1 (by change (2 * ρ ^ 6) * 2 ≤ min rw η; nlinarith only [hhboot])
    (by simpa only [mul_one] using hhη) hζ hβ hν hCtRw
    le_rfl (hdriftFor CgeoWin hWinC) hdR hdR hρchartStrict le_rfl hd
    (by convert hgeom using 1 <;> norm_num) hsizeStrict hentrance hancient
    houter hcubicξ (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hinnerCore)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hinnerChart)
    (by simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hchart)
    (by simpa only [mul_assoc, mul_comm, mul_left_comm] using hsep) hbufferStrict
    N k hk hkN htarget S hS X hX hweighted hcur hdeeper
  obtain ⟨Y, hY, hweightedY, hcurY, hparticlesY⟩ := hwindow'
  have hparticlesPast : ∀ t ∈ Icc (0 : ℝ) entrance,
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
      ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * radScale R ρ (k - 1) := by
    intro t ht
    let τold := ampScale A₀ b k * t
    have htT : t ∈ Icc (0 : ℝ) T := (hX.mem t ht).1
    have hτold : τold ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance) :=
      ⟨mul_nonneg (hAmp k).le ht.1, mul_le_mul_of_nonneg_left ht.2 (hAmp k).le⟩
    have hclockOld : physicalTimeFromNormalized (ampScale A₀ b k) 0 τold = t := by
      simp only [τold, physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp k).ne']
    let Z := canonicalPrefixAbsoluteFamily A₀ b R ρ k 0 X τold
    let u : ℕ → ℝ := fun l => ampScale A₀ b l * 0 + (b : ℝ) ^ (k - l) * τold
    let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
    obtain ⟨G, _hG, _hownq⟩ := hmaterial (core := core) (δ := η) (C₀ := 2) (K := 1)
      hs hA.le hbR hR hRhalf hρ hρ1 hρb hq hqE le_rfl (hdriftFor Cmaterial hMaterialC)
      hdRquarter hentrance.le hkN S hS X hX t ht
      hηquarter hcorei (by norm_num) hh1 (by norm_num) (by simpa only [mul_one] using hhη)
      Z u φ (hweighted τold hτold) (hcur τold hτold) (by
        intro p
        have heq := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
          (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := (b : ℝ)) hR hρ k 0 τold X p.1)
        rw [hclockOld] at heq
        simpa only [Z, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
          Pi.smul_apply] using heq.symm)
    exact P.actual_inner_particle_radius_reset hs hR hRhalf hρ hρ1 hk hkN htT G (hdeeper t ht)
  refine ⟨Y, hY, hweightedY, hcurY, hparticlesY, hparticlesPast, ?_⟩
  intro t ht
  let τold := ampScale A₀ b k * t
  let τnew := ampScale A₀ b (k - 1) * t
  have hentranceH : entrance ≤ Hparent := le_add_of_nonneg_right (div_nonneg hDparent.le (hAmp _).le)
  have htY : t ∈ Icc (0 : ℝ) Hparent := ⟨ht.1, ht.2.trans hentranceH⟩
  have hτold : τold ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance) :=
    ⟨mul_nonneg (hAmp k).le ht.1, mul_le_mul_of_nonneg_left ht.2 (hAmp k).le⟩
  have hclockOld : physicalTimeFromNormalized (ampScale A₀ b k) 0 τold = t := by
    simp only [τold, physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp k).ne']
  have hclockNew : physicalTimeFromNormalized (ampScale A₀ b (k - 1)) 0 τnew = t := by
    simp only [τnew, physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp _).ne']
  have hr := hreset hs hA hbR hR hRhalf hρ hρ1 hρb hq hqE le_rfl
    (hdriftFor Creset hResetC) hdRquarter N k hk hkN S hX hY t ht htY
    0 τold 0 τnew hclockOld hclockNew hh (hweighted τold hτold)
  simpa only [one_mul] using hr

end CircularMaterialTransferProfile
end Euler2D

end
