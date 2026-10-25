module

public import RequestProject.Euler.CircularCanonicalHandoffEntry
public import RequestProject.Euler.CircularAncientObservationFromParent
public import RequestProject.Euler.ActualFinitePlanarSourceIdentity

/-! The actual canonical capture supplies its own entry geometry.
The SAME original Euler system and actual parent prefix then give
the ORIGINAL ancient/positive moment on the child observation window,
including the literal boxed physical moment used by the force theorem.
Neither entry domain images nor an analytic moment bound is assumed. -/

@[expose] public section

set_option maxHeartbeats 32000000
set_option maxRecDepth 8000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_eventually_actualCanonical_observed_child_boxed_moment
    {sCanon : ℝ} (hsCanon : sCanon ≤ 0)
    {s A₀ b q T core C₀ Cw Ccur D η δ Cmatch : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T)
    (hcore : 0 < core) (hcorei : ∀ i, core ≤ 3 * circularContourRadii i / 4)
    (hC₀ : 0 < C₀) (hCw : 0 ≤ Cw) (hCcur : 0 ≤ Ccur) (hD : 0 ≤ D)
    (hη : 0 < η) (hδ : 0 < δ) (hδa : δ ≤ cellA / 4) :
    ∃ Cgeo > 0, ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let h := C₀ * ρ ^ 6
      ∀ {Hglob achild aparent d Dchild Dparent : ℝ}, Hglob ≤ T →
      5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * Hglob < d → d * ρ ≤ 1 / 4 →
      0 ≤ Dchild → 0 ≤ Dparent →
      ∀ (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N),
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) N) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ u ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward u) volume volume ∧
        MeasurePreserving (S.backward u) volume volume) →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ achild Hglob hρ hρ hkN S Dchild X →
      ∀ captureEntrance exit entrance angle : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) captureEntrance exit = entrance →
      entrance ∈ Icc (0 : ℝ) Dchild →
      (let y := canonicalPrefixAlignedCurrentCell A₀ b ρ ρ k captureEntrance X;
        ‖circularCoRotationCLM γ exit (y exit) - contourRotationFamilyLittleCLM γ angle
          (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ ≤ Cmatch * ρ ^ 3) →
      ∀ Y : ℝ → FiniteCircularIndex (k - 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ aparent Hglob hρ hρ
        ((Nat.sub_le k 1).trans hkN) S Dparent Y →
      (∀ τ ∈ Icc (0 : ℝ) D,
        physicalTimeFromNormalized (ampScale A₀ b k) entrance τ ∈ Icc (0 : ℝ) Dparent) →
      (∀ τ ∈ Icc (0 : ℝ) D,
        weightedFamilyNorm h (k - 1)
          (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (k - 1) entrance Y (b * τ)) ≤ Cw * h) →
      (∀ τ ∈ Icc (0 : ℝ) D,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ (k - 1) entrance Y (b * τ) (k - 1)‖ ≤ Ccur * h) →
      ∀ τ ∈ Icc (0 : ℝ) D,
        let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance τ;
        ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N k) t)) 4 -
          (ampScale A₀ b k : ℂ) * (radScale ρ ρ k : ℂ) ^ 6 *
            Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b k + angle : ℝ) : ℂ)) * I)) *
              P.moment (sCanon + τ)‖ ≤ ampScale A₀ b k * radScale ρ ρ k ^ 6 * η := by
  obtain ⟨Ce, hCe, hentry⟩ := P.exists_uniform_actualCanonical_handoff_entry
  obtain ⟨Co, hCo, δentry, hδentry, hobserve⟩ :=
    P.exists_eventually_actualFinite_ancient_moment_close_of_parent hsCanon
      hs hA hb hb1 hq hqE hT hcore hcorei hC₀ hCw hCcur hD hη hδ hδa
  obtain ⟨Cl, hCl, hlocalize⟩ := P.exists_uniform_actualFinite_boxed_label_eq_singlePlanar
  let Cgeo := Ce + Co + Cl + 1
  have hCgeo : 0 < Cgeo := by dsimp only [Cgeo]; positivity
  have hCeGeo : Ce ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCo, hCl]
  have hCoGeo : Co ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCe, hCl]
  have hClGeo : Cl ≤ Cgeo := by dsimp only [Cgeo]; linarith only [hCe, hCo]
  have hrho := Real.tendsto_exp_neg_atTop_nhds_zero
  have hsmall : Tendsto (fun ξ : ℝ => Cmatch * Real.exp (-ξ) ^ 3) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (3 : ℕ) ≠ 0), mul_zero] using (hrho.pow 3).const_mul Cmatch
  have hhalf : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) ≤ 1 / 2 :=
    (hrho.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono (fun _ ht => ht.le)
  have hρb : ∀ᶠ ξ : ℝ in atTop, Real.exp (-ξ) < b := hrho.eventually (gt_mem_nhds hb)
  have hcloseEntry : ∀ᶠ ξ : ℝ in atTop, Cmatch * Real.exp (-ξ) ^ 3 < δentry :=
    hsmall.eventually (gt_mem_nhds hδentry)
  refine ⟨Cgeo, hCgeo, ?_⟩
  filter_upwards [hobserve, hhalf, hρb, hcloseEntry] with ξ hobsξ hhalf hρb hentrySmall
  try dsimp only
  let ρ := Real.exp (-ξ)
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hρ1 : ρ ≤ 1 := hhalf.trans (by norm_num)
  intro Hglob achild aparent d Dchild Dparent hglobT hdrift hdR hDchild hDparent N k hk hkN S hS harea
    X hX captureEntrance exit entrance angle hclock hentrance hmatch Y hY hwindow hweighted hcur
  have hHglob : 0 ≤ Hglob := hDchild.trans (hX.mem Dchild ⟨hDchild, le_rfl⟩).1.2
  have hden : 0 < 1 - ρ / b := sub_pos.mpr ((div_lt_one hb).mpr hρb)
  have hdriftC (C : ℝ) (hC : C ≤ Cgeo) : 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < d := by
    have hmul := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hA.le) hden.le) hHglob
    exact lt_of_le_of_lt (add_le_add le_rfl hmul) hdrift
  obtain ⟨hscale, himages, herror⟩ := hentry hs hA.le hb hρ hhalf hρ hρ1 hρb hq hqE
    hglobT (hdriftC Ce hCeGeo) hdR N S hkN hDchild X hX entrance hentrance
      captureEntrance exit sCanon angle hclock
  let y := canonicalPrefixAlignedCurrentCell A₀ b ρ ρ k captureEntrance X
  let W := circularCanonicalHandoffAlignmentCLM γ sCanon angle exit (y exit)
  let θentry := entrance * finiteAncestorAngularVelocity A₀ b k + angle
  let β := fun i : Fin 2 => circularContourAngularVelocities i *
    (ampScale A₀ b k * captureEntrance + exit - sCanon) - angle
  let Zend := fun i : Fin 2 => (X entrance (Fin.last k, i)).val
  have hnear : ‖W - P.ancient sCanon‖ < δentry := by
    rw [herror]
    exact hmatch.trans_lt hentrySmall
  have heT : entrance ∈ Icc (0 : ℝ) T :=
    ⟨hentrance.1, ((hX.mem entrance hentrance).1.2).trans hglobT⟩
  have hobs := hobsξ hglobT (hdriftC Co hCoGeo) hdR hDparent N k hk hkN S hS harea
    entrance heT Y hY hwindow hweighted hcur θentry β W Zend hscale himages hnear
  intro τ hτ
  let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance τ
  have ht : t ∈ Icc (0 : ℝ) Hglob := (hY.mem t (hwindow τ hτ)).1
  have hboxed := hlocalize hs hA.le hb hρ hhalf hρ hρ1 hρb hq hqE hHglob hglobT
    (hdriftC Cl hClGeo) (hdR.trans_lt (by norm_num : (1 / 4 : ℝ) < 1)) N S t ht k
  change ‖momentN (boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ N k) t)) 4 -
    (ampScale A₀ b k : ℂ) * (radScale ρ ρ k : ℂ) ^ 6 *
      Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b k + angle : ℝ) : ℂ)) * I)) *
        P.moment (sCanon + τ)‖ ≤ _
  rw [hboxed]
  have htheta : θentry + (finiteAncestorAngularVelocity A₀ b k / ampScale A₀ b k) * τ =
      t * finiteAncestorAngularVelocity A₀ b k + angle := by
    dsimp only [θentry, t, physicalTimeFromNormalized]
    ring
  have hh := (hobs τ hτ).2.le
  rw [htheta] at hh
  exact hh

end CircularMaterialTransferProfile
end Euler2D

end
