module

public import RequestProject.Euler.CircularChildObservationGeometry
public import RequestProject.Euler.CircularActualAncientSectionObservation

/-! Original ancient-moment observations from an actual parent
prefix. The true ancestor tubes and their child-weighted deviations
are constructed here, instead of being assumed as observation data. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 7500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

theorem physicalTime_parent_child_clock {A₀ b : ℝ} (hA : 0 < A₀) (hb : 0 < b)
    {k : ℕ} (hk : 0 < k) (entrance τ : ℝ) :
    physicalTimeFromNormalized (ampScale A₀ b (k - 1)) entrance (b * τ) =
      physicalTimeFromNormalized (ampScale A₀ b k) entrance τ := by
  have hAc : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hpower : k - (k - 1) = 1 := by omega
  have hratio : ampScale A₀ b (k - 1) / ampScale A₀ b k = b := by
    simpa only [hpower, pow_one] using ampScale_ratio_eq_pow hA.ne' hb.ne' (Nat.sub_le k 1)
  have hrel : ampScale A₀ b (k - 1) = b * ampScale A₀ b k := (div_eq_iff hAc.ne').mp hratio
  unfold physicalTimeFromNormalized
  rw [hrel]
  congr 1
  field_simp [hb.ne', hAc.ne']

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualFinite_ancient_moment_close_of_parent
    {sCanon : ℝ} (hsCanon : sCanon ≤ 0)
    {s A₀ b q T core C₀ Cw Ccur D η δ : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hcore : 0 < core) (hcorei : ∀ i, core ≤ 3 * circularContourRadii i / 4)
    (hC₀ : 0 < C₀) (hCw : 0 ≤ Cw) (hCcur : 0 ≤ Ccur) (hD : 0 ≤ D)
    (hη : 0 < η) (hδ : 0 < δ) (hδa : δ ≤ cellA / 4) :
    ∃ Cgeo > 0, ∃ δentry > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {Hglob a d Dphys : ℝ}, Hglob ≤ T →
      5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * ρ ≤ 1 / 4 → 0 ≤ Dphys →
      ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ entrance : ℝ, ∀ he : entrance ∈ Icc (0 : ℝ) T,
      ∀ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ a Hglob hρ hρ ((Nat.sub_le k 1).trans hkN) S Dphys Y →
      (∀ τ ∈ Icc (0 : ℝ) D,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) Dphys) →
      (∀ τ ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h (k - 1)
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (k - 1) entrance Y (b * τ)) ≤ Cw * h) →
      (∀ τ ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (k - 1) entrance Y (b * τ) (k - 1)‖ ≤ Ccur * h) →
      ∀ (θentry : ℝ) (β : Fin 2 → ℝ),
      ∀ (W : Fin 2 → LittleContourSpace γ) (Zend : Fin 2 → ContourC1Space γ),
      (∀ i, Zend i = radScale ρ ρ k • ContourC1Space.complexScale (Complex.exp ((θentry : ℂ) * I))
        (contourParameterShiftC1 (β i) (W i).val)) →
      (∀ i, S.forward entrance '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 ρ ρ (P.ancient s) N (⟨k, Nat.lt_succ_of_le hkN⟩, i)).val)) =
          complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) →
      ‖W - P.ancient sCanon‖ < δentry →
      ∀ τ ∈ Icc (0 : ℝ) D,
        ‖planarFourthMoment (S.rotatingNormalizedPlanarLabelSource
            (P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k) (ampScale A₀ b k) (radScale ρ ρ k)
            (θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ)
            (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ)) - P.moment (sCanon + τ)‖ < η ∧
        ‖momentN (fun z => P.finiteSinglePlanarInitialLabel s A₀ b ρ ρ N k
            (S.backward (physicalTimeFromNormalized (ampScale A₀ b k) entrance τ) (complexTorusPoint z))) 4 -
          (ampScale A₀ b k : ℂ) * (radScale ρ ρ k : ℂ) ^ 6 *
            Complex.exp (-(4 * ((θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ : ℝ) : ℂ) * I)) *
            P.moment (sCanon + τ)‖ < ampScale A₀ b k * radScale ρ ρ k ^ 6 * η := by
  obtain ⟨Cgeo, hCgeo, hgeometry⟩ := P.exists_uniform_actualParent_child_observation_geometry
  obtain ⟨δentry, hδentry, hmoment⟩ :=
    P.exists_eventually_actualFinite_ancient_section_moment_close (K := max Cw Ccur) hsCanon
      hs hA hb hb1 hq hqE hT hcore hC₀ (le_max_of_le_left hCw) hD hη
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
  filter_upwards [hmoment, hsmallw, hsmallcur, hhalf, hρb, hone] with ξ hξ hsmallw hsmallcur hhalf hρb hh1
  try dsimp only
  let ρ := Real.exp (-ξ)
  let h := C₀ * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ ≤ 1 := hhalf.trans (by norm_num)
  intro Hglob a d Dphys hglobT hdrift hdR hDphys N k hk hkN S hS harea entrance he
    Y hY hwindow hZ hcur θentry β W Zend hscale himages hnear
  have hpoint (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) D) :=
    hgeometry hs hA hb hρ hhalf hρ hρ1 hρb hq hqE hglobT hdrift hdR hDphys N k hk hkN S hS Y hY
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
