module

public import RequestProject.Euler.CircularExistingParentPrefix
public import RequestProject.Euler.CircularCanonicalJointFixedWindow

/-! Construct the actual parent prefix beyond the child exit.
Before the exit it agrees with the old material particles. Afterwards
the genuine joint fixed-window estimates close continuation. The
future parent trajectory is a conclusion, not an input. -/

@[expose] public section

set_option maxHeartbeats 64000000
set_option maxRecDepth 8500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actual_parent_observation_window :
    let L := circularCanonicalCellNormBudget hγ hγ1
    ∃ Kself : ℝ≥0, 0 < Kself ∧ ∃ rw > 0, ∃ Ctw > 0,
      ∀ b : ℝ≥0, 0 < b → b < 1 →
      ∀ {D C₀ K η νbar : ℝ}, 0 < D → 2 ≤ C₀ → 0 ≤ K →
      0 < η → η ≤ cellA / 16 → η ≤ (1 - cellA) / 16 →
      ∃ Cgeo Ctc Cdc Cr Kr Ccur Cobs : ℝ,
      0 < Cgeo ∧ 0 < Ctc ∧ 0 < Cdc ∧ 0 < Cr ∧ 0 < Kr ∧ 0 < Ccur ∧ 0 < Cobs ∧
      let Cb := radialStageRadiusConstant Cr 2 b
      ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {s A₀ R q T Hglob a d entrance : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      let Cu := finiteInnerLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L
      let Cl := finiteOuterLabelLittleRowCoefficient (γ : ℝ) (cellA / 2) L L
      let CtRw := Ctw * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L * R ^ 8
      let β := 3 * CtRw + weightedInteractionRowFeedback b Cu Cl C₀ ρ
      R ≤ 1 / 2 → R ≤ ρ → ρ ≤ 1 → ρ ≤ b / 2 → ρ ≤ cellA / 256 → ρ ^ 2 ≤ b / 2 →
      (5 / 4 : ℝ) * ρ ≤ cellA → 10 * ρ ≤ cellA / 2 → 8 * L * ρ ≤ cellA / 2 →
      h ≤ 1 → h * 2 ≤ min rw η → h * K ≤ η → C₀ * ρ ^ 8 ≤ 1 / 2 →
      0 ≤ β → ((b * Kself : ℝ≥0) : ℝ) + β ≤ νbar → CtRw ≤ 1 →
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d →
      d * R ≤ 1 / 16 → d * R ≤ a → (5 / 4 : ℝ) * R < a → a ≤ 1 / 16 → 0 < d →
      (L + 1) * R ≤ a / 2 → R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4 →
      0 < entrance →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      (2 * (b : ℝ) * C₀ * 2 * (Cl + Ctc * finiteTorusLabelLittleRowCoefficient (γ : ℝ) L)) * ρ ^ 2 ≤ 1 →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ (cellA / 2) d η * Cb ^ 3 *
        ρ ^ 2 * (1 + D) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + D) ≤ (cellA / 2) / 2 → Cb * ρ * (1 + D) ≤ d →
      Cb * ρ * R * (1 + D) ≤ a → 8 * (Cb * ρ * (1 + D)) ≤ cellA / 2 →
      max 2 (Cb * (1 + D)) * ρ < cellA / 64 →
      ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      entrance + D / ampScale A₀ b (k - 1) < Hglob →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) hR (Real.exp_pos (-ξ)) hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := (b : ℝ)) (ρ := ρ) (q := q) hs hR (Real.exp_pos (-ξ))) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR (Real.exp_pos (-ξ)) hkN S entrance X →
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance),
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance),
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ k‖ ≤ η) →
      (∀ t ∈ Icc (0 : ℝ) entrance, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t z - torusCenter‖ ≤ 2 * radScale R ρ k) →
      ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR (Real.exp_pos (-ξ))
          ((Nat.sub_le k 1).trans hkN) S (entrance + D / ampScale A₀ b (k - 1)) Y ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          weightedFamilyNorm h (k - 1)
            (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y τ) ≤ Cobs * h) ∧
        (∀ τ ∈ Icc (0 : ℝ) D,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y τ (k - 1)‖ ≤ Ccur * h) ∧
        ∀ τ ∈ Icc (0 : ℝ) D, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
          ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b (k - 1)) entrance τ) z - torusCenter‖ ≤
            Cb * ρ * radScale R ρ (k - 1) * (1 + τ) := by
  dsimp only
  obtain ⟨Kself, hKself, rw, hrw, Ctw, hCtw, hjoint⟩ :=
    P.exists_uniform_actualCanonical_joint_fixed_window_bound
  obtain ⟨Ce, hCe, hextend⟩ := P.exists_uniform_actualPrefix_trajectory_or_event
  obtain ⟨Cx, hCx, hreset⟩ := P.exists_uniform_actualCanonical_crossPrefix_weighted_reset
  obtain ⟨Cg, hCg, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  refine ⟨Kself, hKself, rw, hrw, Ctw, hCtw, ?_⟩
  intro b hb hb1 D C₀ K η νbar hD hC₀ hK hη hηa hηgap
  have hbR : 0 < (b : ℝ) := hb
  have hηquarter : η ≤ cellA / 4 := by linarith only [hηa, cellA_pos]
  have hcore (i : Fin 2) : cellA / 2 ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    linarith only [hi, cellA_pos]
  obtain ⟨Cwin, Ctc, Cdc, Cr, Kr, Ccur, Cobs, hCwin, hCtc, hCdc, hCr, hKr, hCcur, hCobs, hwindow⟩ :=
    hjoint b hb hb1 (νbar := νbar) (by norm_num : (0 : ℝ) ≤ 2) hD hC₀ hK hη hηquarter (by norm_num : (0 : ℝ) < 2)
  let Cgeo := max Cwin (max Ce (max Cx (max Cg Cs)))
  have hCwinC : Cwin ≤ Cgeo := le_max_left _ _
  have hCeC : Ce ≤ Cgeo := (le_max_left _ _).trans (le_max_right _ _)
  have hCxC : Cx ≤ Cgeo := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCgC : Cg ≤ Cgeo := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hCsC : Cs ≤ Cgeo := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hsmall (A : ℝ) : ∀ᶠ ξ : ℝ in atTop, A * (C₀ * Real.exp (-ξ) ^ 6) ≤ η := by
    have he : Tendsto (fun ξ : ℝ => A * (C₀ * Real.exp (-ξ) ^ 6)) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using
        ((Real.tendsto_exp_neg_atTop_nhds_zero.pow 6).const_mul C₀).const_mul A
    exact (he.eventually (gt_mem_nhds hη)).mono (fun _ ht => ht.le)
  refine ⟨Cgeo, Ctc, Cdc, Cr, Kr, Ccur, Cobs, hCwin.trans_le hCwinC, hCtc, hCdc,
    hCr, hKr, hCcur, hCobs, ?_⟩
  filter_upwards [hwindow (half_pos cellA_pos) hcore, hsmall Ccur, hsmall Cobs] with ξ hξ hcurSmall hobsSmall
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  let Cb := radialStageRadiusConstant Cr 2 b
  intro s A₀ R q T Hglob a d entrance _ hs hA hR hq hqE
    hRmax hRρ hρ1 hρhalf hρsmall hhalf hρcore hsepU hsepL hh1 hhboot hhK hζ hβ hνup hCtRw
    hglobT hdrift hdR hdRa hRa ha16 hdpos hgeom hsize he hancient
    houter hcubic hinnerCore hinnerChart hchart hsep hbufferρ N k hk hkN htarget S hS X hX
    hZold hcurOld hdeeper
  have hρ : 0 < ρ := Real.exp_pos _
  have hC₀pos : 0 < C₀ := by linarith only [hC₀]
  have hh : 0 < h := mul_pos hC₀pos (pow_pos hρ 6)
  have hρb : ρ < (b : ℝ) := hρhalf.trans_lt (by linarith only [hbR])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hbR).mpr hρb)
  have hAmp (l : ℕ) : 0 < ampScale A₀ b l := div_pos hA (pow_pos hbR l)
  let Hcap := entrance + D / ampScale A₀ b (k - 1)
  have heH : entrance ≤ Hcap := le_add_of_nonneg_right (div_nonneg hD.le (hAmp _).le)
  have hHcap : 0 < Hcap := he.trans_le heH
  have hHglob : 0 < Hglob := hHcap.trans htarget
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ Cgeo) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob.le)).trans_lt hdrift
  have hdRquarter : d * R ≤ 1 / 4 := hdR.trans (by norm_num)
  have hρ128 : ρ ≤ cellA / 128 := by linarith only [hρsmall, cellA_pos]
  have ha : 0 < a := (by positivity : 0 < (5 / 4 : ℝ) * R).trans hRa
  have hclock (l : ℕ) (t : ℝ) :
      physicalTimeFromNormalized (ampScale A₀ b l) 0 (ampScale A₀ b l * t) = t := by
    simp only [physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp l).ne']
  have hglobal := hsupport hs hA.le hbR hR hRmax hρ hρ1 hρb hq hqE hHglob.le hglobT
    (hdriftFor Cs hCsC) (hdR.trans_lt (by norm_num)) N S
  have hsupp : ∀ t ∈ Icc (0 : ℝ) Hglob, ∀ z ∈ torusBox,
      a < ‖z - torusCenter‖ → S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t z = 0 := by
    intro t ht z hz hn
    exact hglobal t ht z hz (hdRa.trans_lt hn)
  let rp := radScale R ρ (k - 1)
  let Cbuf := max 2 (Cb * (1 + D))
  let ai₀ := Cbuf * ρ * rp
  let ai := (cellA / 64) * rp
  have hrp : 0 < rp := radScale_pos hR hρ (k - 1)
  have hrpR : rp ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hai₀ : 0 ≤ ai₀ := by dsimp only [ai₀, Cbuf]; positivity
  have hbuffer : ai₀ < ai := mul_lt_mul_of_pos_right hbufferρ hrp
  have hai1 : ai < 1 := by
    have hm := mul_le_mul_of_nonneg_right cellA_lt_one.le hrp.le
    dsimp only [ai]
    nlinarith only [hm, hrpR, hRmax]
  have hsepBuffer (p : FiniteCircularIndex (k - 1)) : 32 * ai ≤ finiteCircularInterfaceRadius R ρ p := by
    have hmono : rp ≤ radScale R ρ p.1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ.le hρ1 (Nat.le_of_lt_succ p.1.isLt)) hR.le
    have hm₁ := mul_le_mul_of_nonneg_left hmono cellA_pos.le
    have hm₂ := mul_le_mul_of_nonneg_right (circularContourRadii_bounds p.2).2.1 (radScale_pos hR hρ p.1).le
    dsimp only [ai, finiteCircularInterfaceRadius]
    nlinarith only [hm₁, hm₂, mul_pos cellA_pos hrp]
  have hKh : K * h ≤ η := by simpa only [mul_comm] using hhK
  have hnewK : 0 ≤ K * h := mul_nonneg hK hh.le
  have hnewSmall : h * (K * h) ≤ η := by
    calc
      _ = (h * K) * h := by ring
      _ ≤ h * K := mul_le_of_le_one_right (mul_nonneg hh.le hK) hh1
      _ ≤ η := hhK
  have hpast (D' : ℝ) (Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ)
      (hY : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
        ((Nat.sub_le k 1).trans hkN) S D' Y) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D') (hte : t ≤ entrance) :
      (∃ β : FiniteCircularIndex (k - 1) → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) ∧
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
        ‖S.forward t z - torusCenter‖ ≤ 2 * ρ * rp := by
    let τold := ampScale A₀ b k * t
    let τnew := ampScale A₀ b (k - 1) * t
    have htold : t ∈ Icc (0 : ℝ) entrance := ⟨ht.1, hte⟩
    have hτold : τold ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance) :=
      ⟨mul_nonneg (hAmp k).le ht.1, mul_le_mul_of_nonneg_left hte (hAmp k).le⟩
    have htoldClock : physicalTimeFromNormalized (ampScale A₀ b k) 0 τold = t := hclock k t
    have htnewClock : physicalTimeFromNormalized (ampScale A₀ b (k - 1)) 0 τnew = t := hclock (k - 1) t
    have hr := hreset hs hA hbR hR hRmax hρ hρ1 hρb hq hqE hglobT (hdriftFor Cx hCxC)
      hdRquarter N k hk hkN S hX hY t htold ht 0 τold 0 τnew htoldClock htnewClock hh (hZold τold hτold)
    have htube := canonicalPrefix_material_tube_of_joint_controls hγ hγ1 A₀ b hR hρ (k - 1) 0 τnew Y
      hh hh1 hnewK hnewSmall hr.1 (hr.2.1.trans hKh)
    rw [htnewClock] at htube
    let Z := canonicalPrefixAbsoluteFamily A₀ b R ρ k 0 X τold
    let u : ℕ → ℝ := fun l => ampScale A₀ b l * 0 + (b : ℝ) ^ (k - l) * τold
    let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
    obtain ⟨G, _hG, _hownq⟩ := hgeo (core := cellA / 2) (δ := η) (C₀ := C₀) (K := K)
      hs hA.le hbR hR hRmax hρ hρ1 hρb hq hqE hglobT (hdriftFor Cg hCgC) hdRquarter he.le
      hkN S hS X hX t htold hηquarter hcore hC₀pos hh1 hK hhK Z u φ
      (hZold τold hτold) (hcurOld τold hτold) (by
        intro p
        have hh' := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
          (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := (b : ℝ)) hR hρ k 0 τold X p.1)
        rw [htoldClock] at hh'
        simpa only [Z, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
          Pi.smul_apply] using hh'.symm)
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, hte.trans (heH.trans (htarget.le.trans hglobT))⟩
    exact ⟨htube, P.actual_inner_particle_radius_reset hs hR hRmax hρ hρ1 hk hkN htT G (hdeeper t htold)⟩
  have hwindowFor (D' : ℝ) (hDD : D' ≤ Hcap)
      (Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ)
      (hY : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
        ((Nat.sub_le k 1).trans hkN) S D' Y) (heD' : entrance ≤ D') := by
    let H := ampScale A₀ b (k - 1) * (D' - entrance)
    have hH : 0 ≤ H := mul_nonneg (hAmp _).le (sub_nonneg.mpr heD')
    have hHD : H ≤ D := by
      have hu := mul_le_mul_of_nonneg_left hDD (hAmp (k - 1)).le
      have hc : D / ampScale A₀ b (k - 1) * ampScale A₀ b (k - 1) = D := div_mul_cancel₀ _ (hAmp _).ne'
      dsimp only [Hcap] at hu
      dsimp only [H]
      nlinarith only [hu, hc]
    have htimeEnd : entrance + H / ampScale A₀ b (k - 1) ≤ D' := by
      dsimp only [H]
      rw [mul_div_cancel_left₀ _ (hAmp _).ne']
      linarith
    have hτold : ampScale A₀ b k * entrance ∈ Icc (0 : ℝ) (ampScale A₀ b k * entrance) :=
      ⟨mul_nonneg (hAmp k).le he.le, le_rfl⟩
    have hseed := hreset hs hA hbR hR hRmax hρ hρ1 hρb hq hqE hglobT (hdriftFor Cx hCxC)
      hdRquarter N k hk hkN S hX hY entrance ⟨he.le, le_rfl⟩ ⟨he.le, heD'⟩
      0 (ampScale A₀ b k * entrance) entrance 0 (hclock k entrance)
      (by simp only [physicalTimeFromNormalized, zero_div, add_zero]) hh (hZold _ hτold)
    have hstart := (hpast D' Y hY entrance ⟨he.le, heD'⟩ le_rfl).2
    exact hξ hs hA hR hq hqE hRmax hRρ hρ1 hρhalf hhalf hρcore hsepU hsepL hh1 hhboot hζ
      hβ hνup hCtRw hglobT (hdriftFor Cwin hCwinC) hdR ha ha16 hdpos hRa.le hgeom
      (he.le.trans heD') he.le hH hHD hη.le hηquarter hancient houter hcubic hinnerCore hinnerChart hchart hsep
      N (k - 1) ((Nat.sub_le k 1).trans hkN) htimeEnd S hS Y hY hseed.1 hseed.2.1 hstart
  have hcontrol (D' : ℝ) (hDD : D' ≤ Hcap)
      (Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ)
      (hY : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
        ((Nat.sub_le k 1).trans hkN) S D' Y) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D') :
      (∃ β : FiniteCircularIndex (k - 1) → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) ∧
      ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1), ‖S.forward t z - torusCenter‖ ≤ ai₀ := by
    by_cases hte : t ≤ entrance
    · have hp := hpast D' Y hY t ht hte
      refine ⟨hp.1, fun z hz => (hp.2 z hz).trans ?_⟩
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (2 : ℝ) (Cb * (1 + D))) hρ.le) hrp.le
    · have het : entrance ≤ t := (lt_of_not_ge hte).le
      have heD' : entrance ≤ D' := het.trans ht.2
      have hw := hwindowFor D' hDD Y hY heD'
      let τ := ampScale A₀ b (k - 1) * (t - entrance)
      have hτ : τ ∈ Icc (0 : ℝ) (ampScale A₀ b (k - 1) * (D' - entrance)) :=
        ⟨mul_nonneg (hAmp _).le (sub_nonneg.mpr het), mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 entrance) (hAmp _).le⟩
      have htime : physicalTimeFromNormalized (ampScale A₀ b (k - 1)) entrance τ = t := by
        dsimp only [physicalTimeFromNormalized, τ]
        rw [mul_div_cancel_left₀ _ (hAmp _).ne']
        ring
      have hobsK : 0 ≤ Cobs * h := mul_nonneg hCobs.le hh.le
      have hobsη : h * (Cobs * h) ≤ η :=
        (mul_le_of_le_one_left hobsK hh1).trans hobsSmall
      have htube := canonicalPrefix_material_tube_of_joint_controls hγ hγ1 A₀ b hR hρ (k - 1) entrance τ Y
        hh hh1 hobsK hobsη (hw.1 τ hτ) ((hw.2.1 τ hτ).trans hcurSmall)
      rw [htime] at htube
      refine ⟨htube, ?_⟩
      intro z hz
      have hn := hw.2.2 τ hτ z hz
      rw [htime] at hn
      have hτD : τ ≤ D := by
        have hu := mul_le_mul_of_nonneg_left hDD (hAmp (k - 1)).le
        have hc : D / ampScale A₀ b (k - 1) * ampScale A₀ b (k - 1) = D := div_mul_cancel₀ _ (hAmp _).ne'
        dsimp only [Hcap] at hu
        have hh' := mul_le_mul_of_nonneg_left ht.2 (hAmp (k - 1)).le
        dsimp only [τ]
        nlinarith only [hu, hc, hh']
      have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr (by norm_num : (0 : ℝ) ≤ 2) hbR (show (b : ℝ) < 1 from hb1)
      have hrad : Cb * ρ * rp * (1 + τ) ≤ ai₀ := by
        calc
          _ = (Cb * (1 + τ)) * ρ * rp := by ring
          _ ≤ (Cb * (1 + D)) * ρ * rp :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (add_le_add le_rfl hτD) hCb.le) hρ.le) hrp.le
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right (2 : ℝ) (Cb * (1 + D))) hρ.le) hrp.le
      exact hn.trans hrad
  have hexists := hextend (s := s) (A₀ := A₀) (b := (b : ℝ)) (R := R) (ρ := ρ) (q := q)
    (T := T) (Hcap := Hcap) (Hglob := Hglob) (a := a) (ai₀ := ai₀) (ai := ai) (η := η) (c := d)
    (N := N) (k := k - 1)
    hs hA.le hbR hR hRmax hρ hρ128 hρb hq hqE hHcap htarget hglobT (hdriftFor Ce hCeC)
    hdRquarter hRa ha16 hai₀ hbuffer hai1 hη.le hηa hηgap hsize hancient
    ((Nat.sub_le k 1).trans hkN) S hS hsupp hsepBuffer
  try dsimp only at hexists
  have hpath :
      (∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ ((Nat.sub_le k 1).trans hkN) S Hcap Y) ∨
      ∃ t ∈ Icc (0 : ℝ) Hcap, ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ ((Nat.sub_le k 1).trans hkN) S t Y ∧ False :=
    hexists (fun _ _ => False) (by
      intro D' _hD' hDD Y hY _ t ht
      exact hcontrol D' hDD Y hY t ht)
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ ((Nat.sub_le k 1).trans hkN) S Hcap Y := by
    rcases hpath with hy | ⟨t, ht, Y, hY, hf⟩
    · exact hy
    · exact False.elim hf
  have hw := hwindowFor Hcap le_rfl Y hY heH
  have hHnorm : ampScale A₀ b (k - 1) * (Hcap - entrance) = D := by
    dsimp only [Hcap]
    rw [add_sub_cancel_left]
    field_simp [(hAmp (k - 1)).ne']
  rw [hHnorm] at hw
  exact ⟨Y, hY, hw.1, hw.2.1, hw.2.2⟩

end CircularMaterialTransferProfile
end Euler2D

end
