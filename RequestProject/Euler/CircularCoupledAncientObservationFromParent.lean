module

public import RequestProject.Euler.CircularAncientObservationFromParent
public import RequestProject.Euler.CircularCoupledActualAncientSectionObservation

/-! Literal transported moments of the SAME finite Euler hierarchy with
R=rho^10 and A0=cA*(1+xi), compared to the ORIGINAL reference/ancient
profile. Actual material geometry, areas and source identities are kept. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_coupled_ancient_moment_close_of_parent
    {sCanon : ℝ} (hsCanon : sCanon ≤ 0)
    {s cA b q T core C₀ Cw Ccur D η δ : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hcore : 0 < core) (hcorei : ∀ i, core ≤ 3 * circularContourRadii i / 4)
    (hC₀ : 0 < C₀) (hCw : 0 ≤ Cw) (hCcur : 0 ≤ Ccur) (hD : 0 ≤ D)
    (hη : 0 < η) (hδ : 0 < δ) (hδa : δ ≤ cellA / 4) :
    ∃ Cgeo > 0, ∃ δentry > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := C₀ * ρ ^ 6
      ∀ {Hglob a d Dphys : ℝ}, Hglob ≤ T →
      5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * R ≤ 1 / 4 → 0 ≤ Dphys →
      ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T,
      ∀ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ ((Nat.sub_le k 1).trans hkN) S Dphys Y →
      (∀ τ ∈ Icc (0 : ℝ) D,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) Dphys) →
      (∀ τ ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h (k - 1)
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y (b * τ)) ≤ Cw * h) →
      (∀ τ ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ (k - 1) entrance Y (b * τ) (k - 1)‖ ≤ Ccur * h) →
      ∀ (θentry : ℝ) (β : Fin 2 → ℝ),
      ∀ (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ),
      (∀ i, Zend i = radScale R ρ k • ContourC1Space.complexScale (Complex.exp ((θentry : ℂ) * I))
        (contourParameterShiftC1 (β i) (W i).val)) →
      (∀ i, S.forward entrance '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (⟨k, Nat.lt_succ_of_le hkN⟩, i)).val)) =
          complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) →
      ‖W - P.ancient sCanon‖ < δentry →
      ∀ τ ∈ Icc (0 : ℝ) D,
        ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource
            (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k) (ampScale A₀ b k) (radScale R ρ k)
            (θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ)
            (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ)) - P.moment (sCanon + τ)‖ < η ∧
        ‖momentN (fun z => P.finiteSinglePlanarInitialLabel s A₀ b R ρ N k
            (S.backward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) (complexTorusPoint z))) 4 -
          (ampScale A₀ b k : ℂ) * (radScale R ρ k : ℂ) ^ 6 *
            Complex.exp (-(4 * ((θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ : ℝ) : ℂ) * I)) *
            P.moment (sCanon + τ)‖ < ampScale A₀ b k * radScale R ρ k ^ 6 * η := by
  obtain ⟨Cgeo, hCgeo, hgeometry⟩ := P.exists_uniform_actualParent_child_observation_geometry
  obtain ⟨δentry, hδentry, hmoment⟩ :=
    P.exists_eventually_actualFinite_coupled_ancient_section_moment_close (K := max Cw Ccur) hsCanon
      hs hcA hb hb1 hq hqE hT hcore hC₀ (le_max_of_le_left hCw) hD hη
  have he : Tendsto (fun ξ : ℝ => Real.exp (-ξ)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hlim : Tendsto (fun ξ : ℝ => C₀ * Real.exp (-ξ) ^ 6) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] using (he.pow 6).const_mul C₀
  have hlimw : Tendsto (fun ξ : ℝ => (C₀ * Real.exp (-ξ) ^ 6) * (Cw * (C₀ * Real.exp (-ξ) ^ 6)))
      atTop (𝓝 0) := by simpa only [mul_zero, zero_mul] using hlim.mul (hlim.const_mul Cw)
  have hlimcur : Tendsto (fun ξ : ℝ => Ccur * (C₀ * Real.exp (-ξ) ^ 6)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul Ccur
  have hsmallw : ∀ᶠ ξ : ℝ in atTop, (C₀ * Real.exp (-ξ) ^ 6) * (Cw * (C₀ * Real.exp (-ξ) ^ 6)) ≤ δ :=
    (hlimw.eventually (gt_mem_nhds hδ)).mono (fun _ ht => ht.le)
  have hsmallcur : ∀ᶠ ξ : ℝ in atTop, Ccur * (C₀ * Real.exp (-ξ) ^ 6) ≤ δ :=
    (hlimcur.eventually (gt_mem_nhds hδ)).mono (fun _ ht => ht.le)
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 / 2 :=
    (he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ ht => ht.le)
  have hρb : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) < b := he.eventually (gt_mem_nhds hb)
  have hone : ∀ᶠ ξ : ℝ in atTop, C₀ * Real.exp (-ξ) ^ 6 ≤ 1 :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono (fun _ ht => ht.le)
  refine ⟨Cgeo, hCgeo, δentry, hδentry, ?_⟩
  filter_upwards [hmoment, hsmallw, hsmallcur, hhalf, hρb, hone, eventually_ge_atTop (0 : ℝ)] with ξ hξ hsmallw hsmallcur hhalf hρb hh1 hscale
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hscale])
  have hρ1 : ρ ≤ 1 := hhalf.trans (by norm_num)
  have hRρ : R ≤ ρ := by
    simpa only [R, pow_one] using pow_le_pow_of_le_one hρ.le hρ1 (by decide : (1 : ℕ) ≤ 10)
  have hRmax : R ≤ 1 / 2 := hRρ.trans hhalf
  intro Hglob a d Dphys hglobT hdrift hdR hDphys N k hk hkN S hS harea entrance he
    Y hY hwindow hZ hcur θentry β W Zend hscale himages hnear
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) :=
    hgeometry hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys N k hk hkN S hS Y hY
      (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) (hwindow τ hτ) entrance (b * τ)
      (physicalTime_parent_child_clock hA hb hk entrance τ) hδa hcorei hC₀ hh1 hCw hsmallw hsmallcur
      (hZ τ hτ) (hcur τ hτ)
  classical
  let G := fun τ (hτ : τ ∈ Icc (0 : ℝ) D) => Classical.choose (hpoint τ hτ)
  have hweighted := fun τ hτ => Classical.choose_spec (hpoint τ hτ)
  have hwindowT (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) :
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) T :=
    ⟨(hwindow τ hτ).1, ((hY.mem _ (hwindow τ hτ)).1.2).trans hglobT⟩
  exact hξ N k hkN S hS harea entrance he θentry β W Zend hscale himages hnear hwindowT G hweighted

end CircularMaterialTransferProfile
end Euler2D

end
