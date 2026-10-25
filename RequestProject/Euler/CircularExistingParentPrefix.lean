module

public import RequestProject.Euler.CircularActualInnerRadiusReset
public import RequestProject.Euler.CircularCanonicalCrossPrefixReset
public import RequestProject.Euler.CircularFiniteWeightedMaterialTube
public import RequestProject.Euler.CircularFinitePrefixEventContinuation
public import RequestProject.Euler.CircularFiniteUniformSupport
public import RequestProject.Euler.CircularCanonicalControlGeometry

/-! Construct the next outer prefix through the already existing
child interval on the same Euler system. Every provisional parent
prefix agrees with the old material particles; weighted reset and
the genuine inner-radius reset close its continuation bootstrap. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

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

theorem exists_uniform_actual_parent_prefix_through_existing_interval :
    ∃ C > 0, ∀ {s A₀ b R ρ q T Hglob a d D η C₀ K : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρsmall : ρ ≤ cellA / 256) (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 < D → D < Hglob → Hglob ≤ T →
      5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < d →
      d * R ≤ 1 / 16 → d * R ≤ a → (5 / 4) * R < a → a ≤ 1 / 16 →
      0 ≤ η → η ≤ cellA / 16 → η ≤ (1 - cellA) / 16 →
      R * (‖littleCircularReference hγ hγ1‖ + η) < a / 4 →
      (∀ i, ‖(P.ancient s i).val - circularReferenceC1 hγ hγ1 i‖ ≤ η) →
      0 < C₀ → C₀ * ρ ^ 6 ≤ 1 → 0 ≤ K → C₀ * ρ ^ 6 * K ≤ η →
      ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X →
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * D),
        weightedFamilyNorm (C₀ * ρ ^ 6) k
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) (ampScale A₀ b k * D),
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 X τ k‖ ≤ η) →
      (∀ t ∈ Icc (0 : ℝ) D, ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward t y - torusCenter‖ ≤ 2 * radScale R ρ k) →
      ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
          ((Nat.sub_le k 1).trans hkN) S D Y ∧
        ∀ t ∈ Icc (0 : ℝ) D,
          let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) 0 Y
            (ampScale A₀ b (k - 1) * t)
          weightedFamilyNorm (C₀ * ρ ^ 6) (k - 1) x ≤ K * (C₀ * ρ ^ 6) ∧
          ‖x (k - 1)‖ ≤ K * (C₀ * ρ ^ 6) ∧
          ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
            ‖S.forward t y - torusCenter‖ ≤ 2 * ρ * radScale R ρ (k - 1) := by
  obtain ⟨Ce, hCe, hextend⟩ := P.exists_uniform_actualPrefix_trajectory_or_event
  obtain ⟨Cx, hCx, hreset⟩ := P.exists_uniform_actualCanonical_crossPrefix_weighted_reset
  obtain ⟨Cg, hCg, hgeo⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  let C := max Ce (max Cx (max Cg Cs))
  have hCeC : Ce ≤ C := le_max_left _ _
  have hCxC : Cx ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCgC : Cg ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCsC : Cs ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, hCe.trans_le hCeC, ?_⟩
  intro s A₀ b R ρ q T Hglob a d D η C₀ K _ hs hA hb hR hRmax hρ hρ1 hρsmall hρb hq hqE
    hD hDH hglobT hdrift hdR hdRa hRa ha16 hη hηa hηgap hsize hancient hC₀ hh1 hK hhK
    N k hk hkN S hS X hX hZold hcurOld hdeeper
  let h := C₀ * ρ ^ 6
  have hh : 0 < h := mul_pos hC₀ (pow_pos hρ 6)
  have hHglob : 0 < Hglob := hD.trans hDH
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hdriftFor (C₁ : ℝ) (hC₁ : C₁ ≤ C) :
      5 / 4 + (C₁ * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC₁ hA.le) hden.le) hHglob.le)).trans_lt hdrift
  have hdRquarter : d * R ≤ 1 / 4 := hdR.trans (by norm_num)
  have hρ128 : ρ ≤ cellA / 128 := by linarith only [hρsmall, cellA_pos]
  have hηquarter : η ≤ cellA / 4 := hηa.trans (by linarith only [cellA_pos])
  have hAmp (l : ℕ) : 0 < ampScale A₀ b l := div_pos hA (pow_pos hb l)
  have hclock (l : ℕ) (t : ℝ) :
      physicalTimeFromNormalized (ampScale A₀ b l) 0 (ampScale A₀ b l * t) = t := by
    simp only [physicalTimeFromNormalized, zero_add, mul_div_cancel_left₀ t (hAmp l).ne']
  have hglobal := hsupport hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hHglob.le hglobT
    (hdriftFor Cs hCsC) (hdR.trans_lt (by norm_num)) N S
  have hsupp : ∀ t ∈ Icc (0 : ℝ) Hglob, ∀ y ∈ torusBox,
      a < ‖y - torusCenter‖ →
        S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t y = 0 := by
    intro t ht y hy hn
    exact hglobal t ht y hy (hdRa.trans_lt hn)
  let rp := radScale R ρ (k - 1)
  let ai₀ := 2 * ρ * rp
  let ai := (cellA / 64) * rp
  have hrp : 0 < rp := radScale_pos hR hρ (k - 1)
  have hrpR : rp ≤ R := mul_le_of_le_one_right hR.le (pow_le_one₀ hρ.le hρ1)
  have hai₀ : 0 ≤ ai₀ := by dsimp only [ai₀]; positivity
  have hbuffer : ai₀ < ai := by
    have hhρ : 2 * ρ < cellA / 64 := by linarith only [hρsmall, cellA_pos]
    exact mul_lt_mul_of_pos_right hhρ hrp
  have hai1 : ai < 1 := by
    have hm := mul_le_mul_of_nonneg_right cellA_lt_one.le hrp.le
    dsimp only [ai]
    nlinarith only [hm, hrpR, hRmax]
  have hsep (p : FiniteCircularIndex (k - 1)) :
      32 * ai ≤ finiteCircularInterfaceRadius R ρ p := by
    have hmono : rp ≤ radScale R ρ p.1 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ.le hρ1 (Nat.le_of_lt_succ p.1.isLt)) hR.le
    have hm₁ := mul_le_mul_of_nonneg_left hmono cellA_pos.le
    have hm₂ := mul_le_mul_of_nonneg_right (circularContourRadii_bounds p.2).2.1
      (radScale_pos hR hρ p.1).le
    dsimp only [ai, finiteCircularInterfaceRadius]
    nlinarith only [hm₁, hm₂, mul_pos cellA_pos hrp]
  have hKh : K * h ≤ η := by simpa only [mul_comm] using hhK
  have hnewK : 0 ≤ K * h := mul_nonneg hK hh.le
  have hnewSmall : h * (K * h) ≤ η := by
    calc
      _ = (h * K) * h := by ring
      _ ≤ h * K := mul_le_of_le_one_right (mul_nonneg hh.le hK) hh1
      _ ≤ η := hhK
  have hcore (i : Fin 2) : cellA / 2 ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    linarith only [hi, cellA_pos]
  have hcontrol (D' : ℝ) (hDD : D' ≤ D)
      (Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ)
      (hY : P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
        ((Nat.sub_le k 1).trans hkN) S D' Y) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D') :
      let τ := ampScale A₀ b (k - 1) * t
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) 0 Y τ
      weightedFamilyNorm h (k - 1) x ≤ K * h ∧ ‖x (k - 1)‖ ≤ K * h ∧
      (∃ β : FiniteCircularIndex (k - 1) → ℝ, ∀ p,
        ‖contourParameterShiftC1 (β p) (Y t p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
          η * radScale R ρ p.1) ∧
      ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
        ‖S.forward t y - torusCenter‖ ≤ ai₀ := by
    let τold := ampScale A₀ b k * t
    let τnew := ampScale A₀ b (k - 1) * t
    have htold : t ∈ Icc (0 : ℝ) D := ⟨ht.1, ht.2.trans hDD⟩
    have hτold : τold ∈ Icc (0 : ℝ) (ampScale A₀ b k * D) :=
      ⟨mul_nonneg (hAmp k).le ht.1, mul_le_mul_of_nonneg_left htold.2 (hAmp k).le⟩
    have htoldClock : physicalTimeFromNormalized (ampScale A₀ b k) 0 τold = t := hclock k t
    have htnewClock : physicalTimeFromNormalized (ampScale A₀ b (k - 1)) 0 τnew = t := hclock (k - 1) t
    have hr := hreset hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT (hdriftFor Cx hCxC)
      hdRquarter N k hk hkN S hX hY t htold ht 0 τold 0 τnew htoldClock htnewClock hh
      (hZold τold hτold)
    have htube := canonicalPrefix_material_tube_of_joint_controls hγ hγ1 A₀ b hR hρ (k - 1) 0 τnew Y
      hh hh1 hnewK hnewSmall hr.1 (hr.2.1.trans hKh)
    rw [htnewClock] at htube
    let Z := canonicalPrefixAbsoluteFamily A₀ b R ρ k 0 X τold
    let u : ℕ → ℝ := fun l => ampScale A₀ b l * 0 + b ^ (k - l) * τold
    let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
    obtain ⟨G, _hG, _hownq⟩ := hgeo (core := cellA / 2) (δ := η) (C₀ := C₀) (K := K)
      hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT (hdriftFor Cg hCgC) hdRquarter hD.le
      hkN S hS X hX t htold hηquarter hcore hC₀ hh1 hK hhK Z u φ
      (hZold τold hτold) (hcurOld τold hτold) (by
        intro p
        have he := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
          (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k 0 τold X p.1)
        rw [htoldClock] at he
        simpa only [Z, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
          Pi.smul_apply] using he.symm)
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htold.2.trans (hDH.le.trans hglobT)⟩
    have hparticles := P.actual_inner_particle_radius_reset hs hR hRmax hρ hρ1 hk hkN htT G
      (hdeeper t htold)
    exact ⟨hr.1, hr.2.1, htube, hparticles⟩
  have hexists := hextend (s := s) (A₀ := A₀) (b := b) (R := R) (ρ := ρ) (q := q)
    (T := T) (Hcap := D) (Hglob := Hglob) (a := a) (ai₀ := ai₀) (ai := ai) (η := η) (c := d)
    (N := N) (k := k - 1)
    hs hA.le hb hR hRmax hρ hρ128 hρb hq hqE hD hDH hglobT (hdriftFor Ce hCeC)
    hdRquarter hRa ha16 hai₀ hbuffer hai1 hη hηa hηgap hsize hancient
    ((Nat.sub_le k 1).trans hkN) S hS hsupp hsep
  try dsimp only at hexists
  have hpath :
      (∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
          ((Nat.sub_le k 1).trans hkN) S D Y) ∨
      ∃ t ∈ Icc (0 : ℝ) D, ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
          ((Nat.sub_le k 1).trans hkN) S t Y ∧ False :=
    hexists (fun _ _ => False) (by
      intro D' _hD' hDD Y hY _ t ht
      have hc := hcontrol D' hDD Y hY t ht
      exact ⟨hc.2.2.1, hc.2.2.2⟩)
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ
        ((Nat.sub_le k 1).trans hkN) S D Y := by
    rcases hpath with hy | ⟨t, ht, Y, hY, hf⟩
    · exact hy
    · exact False.elim hf
  refine ⟨Y, hY, ?_⟩
  intro t ht
  have hc := hcontrol D le_rfl Y hY t ht
  exact ⟨hc.1, hc.2.1, hc.2.2.2⟩

end CircularMaterialTransferProfile
end Euler2D

end
