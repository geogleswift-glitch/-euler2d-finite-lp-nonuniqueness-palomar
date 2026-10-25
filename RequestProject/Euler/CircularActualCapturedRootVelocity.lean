module

public import RequestProject.Euler.CircularActualRootAnnularDifference

/-! A genuine captured root of the SAME original finite Euler system
departs from the original stationary velocity datum. The displayed
lower bound uses one fixed annular test, independent of the cutoff. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 9000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] phaseDomainC1_group phaseDomainC1_space

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCaptured_root_velocity_departure :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T c δ η Cb D₀ ξ m : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hρinner : ρ ≤ cellA / 4)
        (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hq2 : 2 ≤ q)
        (hsmall : ρ ^ (2 / q) < b)
        (hδ : 0 < δ) (hη : 0 < η) (hηa : η ≤ cellA / 16) (hηmax : 3 * η < 1 / 5)
        (hCb : 0 ≤ Cb) (hm : 0 < m),
      5 / 4 + (C * A₀ / (1 - ρ / b)) * T < c → c * R ≤ 1 / 4 →
      Cb * ρ * (1 + ((6 / sigma) * ξ + D₀)) ≤ cellA / 4 →
      ∀ N ℓ : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      P.HasActualCapturedInnerMomentSection (s := s) (A₀ := A₀) (b := b)
        hR hρ (Nat.zero_le N) S ℓ δ η Cb D₀ ξ m →
      let f := finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N
      let K := complexCurlTestBound (contDiff_annularDepartureTest
        (by positivity : 0 < 3 * η) hηmax hR (hRmax.trans (by norm_num)))
      ∃ t ∈ Ioo (0 : ℝ) (T / 2), 0 < K ∧
        (5 / 2 * A₀ * R ^ 2 * ((m / 2) * δ)) / K ≤
          ‖particleVelocity f S.backward S.backward_area t -
            velocityDatumL2 (A₀ := A₀) (b := b) hR hρ‖ := by
  obtain ⟨C, hC, hAnnular⟩ := P.exists_uniform_actualCanonical_root_annular_difference
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T c δ η Cb D₀ ξ m _ hs hA hb hR hRmax hρ hρ1 hρb hρinner
    hq hqE hq2 hsmall hδ hη hηa hηmax hCb hm hc hcR hparticleBudget N ℓ S hsection
  dsimp only [HasActualCapturedInnerMomentSection] at hsection
  obtain ⟨entrance, he, Ncap, hNcap, hDlog, hphysical, X, hX,
    u, hu, ht, hfour, harea, hchart, hmoment, hcur, hweighted, hparticles⟩ := hsection
  let Dcap := (Ncap : ℝ) * circularCaptureBlockTime ℓ
  have hDcap : 0 ≤ Dcap := hu.1.le.trans hu.2
  have hAk : 0 < ampScale A₀ b 0 := by simpa only [ampScale, pow_zero, div_one] using hA
  let Dphys := entrance + Dcap / ampScale A₀ b 0
  let t := physicalTimeFromNormalized (ampScale A₀ b 0) entrance u
  have hEnd : 0 ≤ Dphys := add_nonneg he (div_nonneg hDcap hAk.le)
  have htend : t ∈ Icc (0 : ℝ) Dphys := by
    refine ⟨ht.1.le, ?_⟩
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hu.2 hAk.le)
  have hparticleRoot : ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N 0,
      ‖S.forward t y - torusCenter‖ ≤ (cellA / 4) * R := by
    intro y hy
    have huLog : u ≤ (6 / sigma) * ξ + D₀ := hu.2.trans hDlog
    have htimeFactor : Cb * ρ * (1 + u) ≤ Cb * ρ * (1 + ((6 / sigma) * ξ + D₀)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl huLog) (mul_nonneg hCb hρ.le)
    calc
      _ ≤ Cb * ρ * radScale R ρ 0 * (1 + u) := hparticles y hy
      _ = (Cb * ρ * (1 + u)) * R := by simp only [radScale, pow_zero]; ring
      _ ≤ (Cb * ρ * (1 + ((6 / sigma) * ξ + D₀))) * R :=
        mul_le_mul_of_nonneg_right htimeFactor hR.le
      _ ≤ (cellA / 4) * R := mul_le_mul_of_nonneg_right hparticleBudget hR.le
  obtain ⟨desc, hsupport, hdifferenceRaw⟩ := hAnnular hs hA.le hb hR hRmax hρ hρ1 hρb
    hρinner hq hqE hsmall le_rfl hc hcR N S hEnd X hX htend hparticleRoot
  let Z := circularCoRotationCLM γ u (canonicalPrefixAlignedCurrentCell A₀ b R ρ 0 entrance X u)
  have hZnear : ‖Z - littleCircularReference hγ hγ1‖ ≤ η := by
    dsimp only [Z]
    rw [norm_circularCoRotationCLM_sub_reference hγ hγ1,
      norm_canonicalPrefixAlignedCurrentCell_sub_reference hγ hγ1]
    exact hcur
  obtain ⟨hTestη, hTestmax, hDin, hinner, houter, hmomentEq⟩ :=
    circular_near_contour_actual_annular_geometry hγ hγ1 hη hηa Z hZnear
  let f := finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
    (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N
  let w := particleCurlL2 f S.backward S.backward_area t
  let z := centeredPlaneToTorusL2 hqE (circularDatumLp (A₀ := A₀) (b := b) hR hρ hq)
  have hf := P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N
  have hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_torusBox] with x hfx hx
    exact (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hx).trans hfx.symm
  have hmean : (∫ x in torusBox, f x) = 0 :=
    (integral_congr_ae (scalarLpLowerToTwo_ae hqE _)).trans
      (P.integral_finiteBaseTorusLp_zero hs hR hRmax hρ hρ1 hq N)
  have hw : (w : R2 → ℝ) =ᵐ[μT]
      S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t :=
    S.particleCurlL2_ae_transportedScalar hwf t
  have hz : (z : R2 → ℝ) =ᵐ[μT] centeredCircularDatum (A₀ := A₀) (b := b) hR hρ hq :=
    centeredPlaneToTorusL2_ae hqE _
  have hcactual : IsCurl (particleVelocity f S.backward S.backward_area t) w :=
    (S.isCurl_particleVelocity_transportedScalar hwf hmean t).congr_ae (EventuallyEq.refl _ _) hw.symm
  have hcdatum : IsCurl (velocityDatumL2 (A₀ := A₀) (b := b) hR hρ) z :=
    (isCurl_velocityDatumL2 hA.le hb hR (hRmax.trans (by norm_num)) hρ hρ1 hq hq2 hsmall).congr_ae
      (EventuallyEq.refl _ _) hz.symm
  have hdiff : (w - z : Lp ℝ 2 μT) =ᵐ[μT]
      physicalAnnularDifference A₀ R
        (contourRadialFill (LittleContourSpace.lift γ (Z 0)))
        (contourRadialFill (LittleContourSpace.lift γ (Z 1))) desc := by
    filter_upwards [Lp.coeFn_sub w z, hw, hz, hdifferenceRaw] with x hsub hwx hzx hdiffx
    simpa only [hsub, Pi.sub_apply, hwx, hzx] using hdiffx
  have hMomJ : (m / 2) * δ ≤ ‖momentJ
      (contourRadialFill (LittleContourSpace.lift γ (Z 0))) 4‖ := by
    rw [hmomentEq]
    exact hmoment
  have hdeparture := velocity_departure_of_annular_geometry hTestη hTestmax hR
    (hRmax.trans (by norm_num)) hA (mul_pos (half_pos hm) hδ) hcactual hcdatum hDin hinner houter
    (annular_descendant_separation_of_root_radius hηa hR desc hsupport) hdiff hMomJ
  exact ⟨t, ht, hdeparture⟩

end CircularMaterialTransferProfile
end Euler2D

end
