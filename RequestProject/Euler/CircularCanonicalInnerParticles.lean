module

public import RequestProject.Euler.CircularCanonicalStageDeviation
public import RequestProject.Euler.CircularFiniteWeightedMaterialTube
public import RequestProject.Euler.CircularFiniteInnerParticleConfinement
public import RequestProject.Euler.CircularFiniteUniformSupport

/-! Real inner particles are confined from the same canonical
weighted/current bootstrap history. The material tubes and global
source support are constructed internally, before using any inner
particle bound in the current or ancestor forcing estimates. -/

@[expose] public section

set_option maxHeartbeats 20000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_inner_particle_confinement {b Cw : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hCw : 0 ≤ Cw) :
    ∃ Cgeo Cr Kr : ℝ, 0 < Cgeo ∧ 0 < Cr ∧ 0 < Kr ∧
      let Cb := radialStageRadiusConstant Cr Cw b
      ∀ {s A₀ R ρ q T Hglob a c d δ Dphys entrance Dcap C₀ K : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρhalf : ρ ≤ b / 2) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 16 →
      0 < c → 0 < d → 0 ≤ Dphys → 0 ≤ entrance → 0 ≤ Dcap → ρ ^ 2 ≤ b / 2 →
      δ ≤ cellA / 4 → (∀ i, c ≤ 3 * circularContourRadii i / 4) →
      1 ≤ C₀ → 0 ≤ K → C₀ * ρ ^ 6 ≤ 1 → C₀ * ρ ^ 6 * K ≤ δ →
      b * finiteEulerUniformRadialCoefficient Kr b R ρ c d δ * Cb ^ 3 *
        ρ ^ 2 * (1 + Dcap) ^ 3 ≤ Cr / 2 →
      Cb * ρ * (1 + Dcap) ≤ c / 2 → Cb * ρ * (1 + Dcap) ≤ d →
      ∀ (N k : ℕ) (hkN : k ≤ N), entrance + Dcap / ampScale A₀ b k ≤ Dphys →
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      IsBanachTimeDomainTrajectoryOn
        (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
          (finiteCircularInterfaceStrength A₀ b))
        (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
        (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) Dphys X →
      let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
      (∀ τ ∈ Icc (0 : ℝ) Dcap, weightedFamilyNorm (C₀ * ρ ^ 6) k (x τ) ≤ K) →
      (∀ τ ∈ Icc (0 : ℝ) Dcap, ‖x τ k‖ ≤ δ) →
      (∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward entrance z - torusCenter‖ ≤ Cw * ρ * radScale R ρ k) →
      ∀ τ ∈ Icc (0 : ℝ) Dcap, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
        ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) z - torusCenter‖ ≤
          Cb * ρ * radScale R ρ k * (1 + τ) := by
  dsimp only
  obtain ⟨Cm, hCm, hmaterial⟩ := P.exists_uniform_actualPrefix_weighted_materialTube
  obtain ⟨Cs, hCs, hsupport⟩ := P.exists_uniform_finiteEuler_support_bound
  obtain ⟨Cr, Kr, hCr, hKr, hconfine⟩ :=
    P.exists_uniform_actualInnerStage_particle_confinement hb hb1 hCw
  let Cgeo := max Cm Cs
  have hCgeo : 0 < Cgeo := hCm.trans_le (le_max_left _ _)
  refine ⟨Cgeo, Cr, Kr, hCgeo, hCr, hKr, ?_⟩
  intro s A₀ R ρ q T Hglob a c d δ Dphys entrance Dcap C₀ K _ hs hA hR hRmax hρ hρ1
    hρhalf hq hqE hglobT hdrift hdR hc hd hDphys he hDcap hhalf hδ hcore hC₀ hK hh1 hhK
    hcubic hinnerCore hinnerChart N k hkN htimeEnd S hS X hX
  let Cb := radialStageRadiusConstant Cr Cw b
  let x := canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance X
  intro hZ hcur hstart
  have hAk : 0 < ampScale A₀ b k := by unfold ampScale; positivity
  have hρb : ρ < b := hρhalf.trans_lt (by linarith only [hb])
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hHglob : 0 ≤ Hglob := (hX.mem 0 ⟨le_rfl, hDphys⟩).1.2
  have hdriftFor (C : ℝ) (hC : C ≤ Cgeo) :
      5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < d :=
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA.le) hden.le) hHglob)).trans_lt hdrift
  have hglobal := hsupport hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hHglob hglobT
    (hdriftFor Cs (le_max_right _ _)) (hdR.trans_lt (by norm_num)) N S
  have hCb : 0 < Cb := radialStageRadiusConstant_pos hCr hCw hb hb1
  have hr : 0 < radScale R ρ k := radScale_pos hR hρ k
  have hC₀pos : 0 < C₀ := by linarith only [hC₀]
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hcur 0 ⟨le_rfl, hDcap⟩)
  let H := entrance + Dcap / ampScale A₀ b k
  have heH : entrance ≤ H := le_add_of_nonneg_right (div_nonneg hDcap hAk.le)
  have hHphys : H ∈ Icc (0 : ℝ) Dphys := ⟨he.trans heH, htimeEnd⟩
  have hHHglob : H ≤ Hglob := (hX.mem H hHphys).1.2
  have hHT : H ≤ T := hHHglob.trans hglobT
  have G : ∀ t ∈ Icc entrance H, P.FiniteOuterMaterialTube s R ρ N k S t c δ := by
    intro t ht
    let τ := ampScale A₀ b k * (t - entrance)
    have hτ : τ ∈ Icc (0 : ℝ) Dcap := by
      refine ⟨mul_nonneg hAk.le (sub_nonneg.mpr ht.1), ?_⟩
      have hh := mul_le_mul_of_nonneg_right ht.2 hAk.le
      have hcanc : Dcap / ampScale A₀ b k * ampScale A₀ b k = Dcap := div_mul_cancel₀ _ hAk.ne'
      dsimp only [H] at hh
      dsimp only [τ]
      nlinarith only [hh, hcanc]
    have htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ = t := by
      dsimp only [physicalTimeFromNormalized, τ]
      field_simp [hAk.ne']
      <;> ring
    have htphys : t ∈ Icc (0 : ℝ) Dphys := ⟨he.trans ht.1, ht.2.trans htimeEnd⟩
    let Y := canonicalPrefixAbsoluteFamily A₀ b R ρ k entrance X τ
    let u : ℕ → ℝ := fun l => ampScale A₀ b l * entrance + b ^ (k - l) * τ
    let φ : ℕ → ℝ := fun l => t * finiteAncestorAngularVelocity A₀ b l
    let htube := hmaterial hs hA.le hb hR hRmax hρ hρ1 hρb hq hqE hglobT
      (hdriftFor Cm (le_max_left _ _)) (hdR.trans (by norm_num)) hDphys hkN S hS X hX t htphys
      hδ hcore hC₀pos hh1 hK hhK Y u φ (hZ τ hτ) (hcur τ hτ) (by
        intro p
        have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => (V p.2).val)
          (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance τ X p.1)
        rw [htime] at hh
        simpa only [Y, canonicalPrefixAbsoluteFamily, dif_pos (Nat.le_of_lt_succ p.1.isLt), φ,
          Pi.smul_apply] using hh.symm)
    exact Classical.choose htube
  have hsmall : ρ ^ 2 < b := hhalf.trans_lt (by linarith only [hb])
  have houter : b * ρ ^ 2 < 1 :=
    (mul_le_of_le_one_right hb.le (pow_le_one₀ hρ.le hρ1)).trans_lt hb1
  have hduration : H - entrance ≤ Dcap / ((1 - b) * ampScale A₀ b k) := by
    have hdenle : (1 - b) * ampScale A₀ b k ≤ ampScale A₀ b k :=
      mul_le_of_le_one_left hAk.le (by linarith only [hb])
    have hh := div_le_div_of_nonneg_left hDcap (mul_pos (sub_pos.mpr hb1) hAk) hdenle
    simpa only [H, add_sub_cancel_left] using hh
  have hparticles := hconfine hs hA hR hRmax hρ hρ1 hρhalf hq hqE hsmall houter hc hd hdR hδ0 hDcap
    hcubic hinnerCore hinnerChart N k hkN S hS he heH hHT hduration
    (fun t ht => hglobal t ⟨he.trans ht.1, ht.2.trans hHHglob⟩) G hstart
  intro τ hτ z hz
  have ht : physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc entrance H := by
    change entrance ≤ entrance + τ / ampScale A₀ b k ∧ entrance + τ / ampScale A₀ b k ≤ H
    exact ⟨le_add_of_nonneg_right (div_nonneg hτ.1 hAk.le),
      add_le_add le_rfl (div_le_div_of_nonneg_right hτ.2 hAk.le)⟩
  have hh := (hparticles _ ht).1 z hz
  have hclock : (1 - b) * ampScale A₀ b k *
      (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ - entrance) = (1 - b) * τ := by
    unfold physicalTimeFromNormalized
    field_simp [hAk.ne']
    <;> ring
  rw [hclock] at hh
  have hlocal : (1 - b) * τ ≤ τ := by nlinarith only [mul_nonneg hb.le hτ.1]
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hlocal)
    (mul_nonneg (mul_nonneg hCb.le hρ.le) hr.le))

end CircularMaterialTransferProfile
end Euler2D

end
