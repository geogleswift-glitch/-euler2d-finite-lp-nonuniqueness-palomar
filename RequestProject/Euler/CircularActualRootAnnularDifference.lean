module

public import RequestProject.Euler.CircularDatumTailSupport
public import RequestProject.Euler.CircularRootObservationDensity
public import RequestProject.Euler.CircularCanonicalPrefixDensity

/-! The actual root vorticity difference of the SAME finite Euler
system and the original infinite datum. Domain transport derives the
root indicators; the real particle fence and the original Lq series
derive the supported descendant remainder. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] phaseDomainC1_group phaseDomainC1_space

lemma root_datumTerm_eq_physical_circular_indicators (A₀ b R ρ : ℝ) (x : R2) :
    datumTerm A₀ b R ρ 0 (x - torusCenter) =
      A₀ * ((5 / 2 : ℝ) * complexDomainIndicator (ball 0 cellA) (normalizedComplexCoordinate R x) -
        (3 / 2 : ℝ) * complexDomainIndicator (ball 0 1) (normalizedComplexCoordinate R x)) := by
  have hnorm : ‖normalizedComplexCoordinate R x‖ = ‖R⁻¹ • (x - torusCenter)‖ :=
    norm_planeComplexEquiv _
  by_cases ha : ‖R⁻¹ • (x - torusCenter)‖ < cellA <;>
    by_cases hb : ‖R⁻¹ • (x - torusCenter)‖ < 1 <;>
    simp [datumTerm, ampScale, radScale, cellW, twoInterface, complexDomainIndicator,
      mem_ball_zero_iff, hnorm, ha, hb] <;> ring

lemma annular_descendant_separation_of_root_radius {η R : ℝ}
    (hηa : η ≤ cellA / 16) (hR : 0 < R) (desc : R2 → ℝ)
    (hsupport : ∀ x, desc x ≠ 0 → ‖x - torusCenter‖ ≤ (cellA / 4) * R) :
    ∀ x ∈ torusBox, desc x ≠ 0 → 2 * (3 * η) ≤ |normalizedRadiusSq R x - 3 / 5| := by
  intro x _ hne
  have hn := hsupport x hne
  have hcapnonneg : 0 ≤ (cellA / 4) * R :=
    mul_nonneg (div_nonneg cellA_pos.le (by norm_num)) hR.le
  have hsq : ‖x - torusCenter‖ ^ 2 ≤ (3 / 80 : ℝ) * R ^ 2 := by
    calc
      _ ≤ ((cellA / 4) * R) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hcapnonneg).mpr hn
      _ = (3 / 80 : ℝ) * R ^ 2 := by
        rw [mul_pow, div_pow, cellA_sq]
        ring
  have hnorm : normalizedRadiusSq R x ≤ 3 / 80 :=
    (div_le_iff₀ (sq_pos_of_pos hR)).mpr hsq
  have hcellUpper : cellA < 4 / 5 := by nlinarith only [cellA_sq, cellA_pos]
  have hηtwenty : η < 1 / 20 := by linarith only [hηa, hcellUpper]
  rw [abs_of_nonpos (by linarith only [hnorm])]
  linarith only [hnorm, hηtwenty]

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_root_annular_difference :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hρinner : ρ ≤ cellA / 4)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hsmall : ρ ^ (2 / q) < b),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {D entrance u : ℝ}, 0 ≤ D →
      ∀ X : ℝ → FiniteCircularIndex 0 → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) Hglob hR hρ (Nat.zero_le N) S D X →
      let t := physicalTimeFromNormalized (ampScale A₀ b 0) entrance u
      t ∈ Icc (0 : ℝ) D →
      (∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N 0,
        ‖S.forward t y - torusCenter‖ ≤ (cellA / 4) * R) →
      let Z := circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ 0 entrance X u)
      let Din := contourRadialFill (LittleContourSpace.lift γ (Z 0))
      let Dout := contourRadialFill (LittleContourSpace.lift γ (Z 1))
      ∃ desc : R2 → ℝ,
        (∀ x, desc x ≠ 0 → ‖x - torusCenter‖ ≤ (cellA / 4) * R) ∧
        (fun x => S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x -
          centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq x) =ᵐ[μT]
            physicalAnnularDifference A₀ R Din Dout desc := by
  obtain ⟨C, hC, hdensity⟩ := P.exists_uniform_actualCanonical_prefix_density
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hρinner hq hqE hsmall
    hglobT hc hcR N S D entrance u hD X hX
  dsimp only
  intro ht hparticles
  let t := physicalTimeFromNormalized (ampScale A₀ b 0) entrance u
  let Z := circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ 0 entrance X u)
  let cap := (cellA / 4) * R
  have hcap1 : cap < 1 := by
    dsimp only [cap]
    nlinarith only [cellA_pos, cellA_lt_one, hR, hRmax]
  have hDglob : D ≤ Hglob := (hX.mem D ⟨hD, le_rfl⟩).1.2
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans (hDglob.trans hglobT)⟩
  have hdeep : ∀ x ∈ torusBox, cap < ‖x - torusCenter‖ →
      P.finiteInnerClusterSource s A₀ b R ρ N 0 S t x = 0 := by
    intro x hx hfar
    apply Finset.sum_eq_zero
    intro j hj
    apply S.transportedScalar_support_of_particle_radius
      (A := P.finiteInnerActiveInitialLabels s A₀ b R ρ N 0) htT hcap1
      (fun y hy => hy.1) ?_ hparticles x hx hfar
    intro y hy hnot
    by_contra hne
    exact hnot ⟨hy, j, hj, hne⟩
  have hactual (x : R2) (hx : x ∈ torusBox) :
      S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
        A₀ * ((5 / 2 : ℝ) * complexDomainIndicator
          (contourRadialFill (LittleContourSpace.lift γ (Z 0))) (normalizedComplexCoordinate R x) -
          (3 / 2 : ℝ) * complexDomainIndicator
          (contourRadialFill (LittleContourSpace.lift γ (Z 1))) (normalizedComplexCoordinate R x)) +
        P.finiteInnerClusterSource s A₀ b R ρ N 0 S t x := by
    have hh := hdensity hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR
      N S (Nat.zero_le N) hD X hX t ht x hx
    have hphase := observed_root_phaseDensity_eq A₀ b R ρ entrance u hR X x
    dsimp only at hphase
    rw [hh]
    simpa only [phaseFiniteContourPatchVorticity, Fintype.sum_prod_type, Nat.reduceAdd, Fin.sum_univ_one] using
      congrArg (fun z => z + P.finiteInnerClusterSource s A₀ b R ρ N 0 S t x) hphase
  let raw : R2 → ℝ := fun x => P.finiteInnerClusterSource s A₀ b R ρ N 0 S t x -
    (centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq x - datumTerm A₀ b R ρ 0 (x - torusCenter))
  let desc : R2 → ℝ := (closedBall torusCenter cap).indicator raw
  refine ⟨desc, ?_, ?_⟩
  · intro x hne
    have hx : x ∈ closedBall torusCenter cap := by
      by_contra hnot
      exact hne (indicator_of_notMem hnot raw)
    exact mem_closedBall_iff_norm.mp hx
  · filter_upwards [ae_restrict_mem measurableSet_torusBox,
      centeredCircularDatum_eq_root_ae_off_inner_scale hA hb hR hρ hρ1 hq hsmall] with x hx hdatum
    have hraw : desc x = raw x := by
      by_cases hin : x ∈ closedBall torusCenter cap
      · exact indicator_of_mem hin raw
      · have hfar : cap < ‖x - torusCenter‖ := by
          simpa only [mem_closedBall_iff_norm, not_le] using hin
        have htail : centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq x =
            datumTerm A₀ b R ρ 0 (x - torusCenter) := by
          apply hdatum
          calc
            R * ρ = ρ * R := mul_comm _ _
            _ ≤ (cellA / 4) * R := mul_le_mul_of_nonneg_right hρinner hR.le
            _ < ‖x - torusCenter‖ := hfar
        simp only [desc, indicator_of_notMem hin, raw, hdeep x hx hfar, htail, sub_self]
    rw [hactual x hx]
    simp only [physicalAnnularDifference, scaledInnerIndicatorDifference, hraw, raw,
      root_datumTerm_eq_physical_circular_indicators]
    ring

end CircularMaterialTransferProfile
end Euler2D

end
