module

public import RequestProject.Euler.CircularActualFirstParentComparison
public import RequestProject.Euler.CircularCoupledCanonicalObservedChildMoment

/-! The ACTUAL physical child moment on the SAME child and parent
prefixes, compared with the ORIGINAL ancient moment at R=rho^10,
A0=cA*(1+xi). All material areas, phases and entrance matching remain. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 40000000
set_option maxRecDepth 9000

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

theorem eventually_actualFirstParent_coupled_observed_child_moment
    {sObs s cA b q T Dobs Cw Ccur Cback η : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hsObs : sObs ≤ 0) (hs : s ≤ 0) (hcA : 0 < cA) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hDobs : 0 ≤ Dobs)
    (hCw : 0 ≤ Cw) (hCcur : 0 ≤ Ccur) (hη : 0 < η) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let R := ρ ^ 10
      let hR := pow_pos hρ 10
      let A₀ := cA * (1 + ξ)
      let h := 2 * ρ ^ 6
      ∀ k : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hR hρ) (k + 1)) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) →
      ∀ Hchild Hparent : ℝ, 0 ≤ Hchild → 0 ≤ Hparent →
      ∀ X : ℝ → FiniteCircularIndex (k + 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ le_rfl S Hchild X →
      ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ (Nat.le_succ k) S Hparent Y →
      ∀ exit entrance angle : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 exit = entrance →
      entrance ∈ Icc (0 : ℝ) Hchild →
      ‖circularCoRotationCLM γ exit (canonicalPrefixAlignedCurrentCell A₀ b R ρ (k + 1) 0 X exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sObs (P.ancient sObs))‖ ≤ Cback * ρ ^ 3 →
      entrance + b * Dobs / ampScale A₀ b k ≤ Hparent →
      (∀ u ∈ Icc (0 : ℝ) Dobs,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u)) ≤ Cw * h) →
      (∀ u ∈ Icc (0 : ℝ) Dobs,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u) k‖ ≤ Ccur * h) →
      ∀ u ∈ Icc (0 : ℝ) Dobs,
        let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u);
        ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) (k + 1)) t)) 4 -
          (ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6 *
            Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b (k + 1) + angle : ℝ) : ℂ)) * I)) *
              P.moment (sObs + u)‖ ≤ ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * η := by
  let core := cellA / 2
  let δ := cellA / 8
  have hcore : 0 < core := half_pos cellA_pos
  have hδ : 0 < δ := div_pos cellA_pos (by norm_num)
  have hδa : δ ≤ cellA / 4 := by dsimp only [δ]; linarith only [cellA_pos]
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  obtain ⟨Cgeo, hCgeo, hobs⟩ := P.exists_eventually_actualCanonical_coupled_observed_child_boxed_moment (Cmatch := Cback) hsObs
    hs hcA hb hb1 hq hqE hT hcore hcorei (by norm_num : (0 : ℝ) < 2) hCw hCcur hDobs hη hδ hδa
  let dc := 4 * Cgeo * cA * T
  let dsupport := fun ξ : ℝ => 2 + dc * (1 + ξ)
  have hdRlim : Tendsto (fun ξ : ℝ => dsupport ξ * Real.exp (-ξ) ^ 10) atTop (𝓝 0) := by
    convert tendsto_circularCapture_log_monomial 1 dc (1 + dc) 10 1 (by decide) using 1
    ext ξ
    dsimp only [dsupport]
    ring
  have hsmallDR := (hdRlim.eventually (gt_mem_nhds
    (by norm_num : (0 : ℝ) < 1 / 4))).mono (fun _ h => h.le)
  have hsmall (A ε : ℝ) (hε : 0 < ε) : ∀ᶠ ξ : ℝ in atTop, A * Real.exp (-ξ) ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => A * Real.exp (-ξ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul A
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  filter_upwards [hobs, hsmall 1 (b / 2) (half_pos hb), hsmallDR, eventually_ge_atTop (0 : ℝ)]
    with ξ hobsξ hρhalf hdR hscale
  simp only [one_mul] at hρhalf
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let d := 2 + 4 * Cgeo * A₀ * T
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hscale])
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hdeq : dsupport ξ = d := by dsimp only [dsupport, dc, d, A₀]; ring
  rw [hdeq] at hdR
  have hdenHalf : (1 / 2 : ℝ) ≤ 1 - ρ / b := by
    have hh : ρ / b ≤ 1 / 2 := (div_le_iff₀ hb).mpr (by nlinarith only [hρhalf])
    linarith only [hh]
  have hdiv : Cgeo * A₀ / (1 - ρ / b) ≤ 2 * Cgeo * A₀ := by
    calc
      _ ≤ Cgeo * A₀ / (1 / 2) :=
        div_le_div_of_nonneg_left (mul_nonneg hCgeo.le hA.le) (by norm_num) hdenHalf
      _ = _ := by ring
  have hdrift : 5 / 4 + (Cgeo * A₀ / (1 - ρ / b)) * T < d := by
    have hh := mul_le_mul_of_nonneg_right hdiv hT
    dsimp only [d]
    nlinarith only [hh, hcat]
  dsimp only
  intro k S hS harea Hchild Hparent hHchild hHparent X hX Y hY exit entrance angle hclock hentrance hmatch hEnd hweighted hcur
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb k)
  have hwindow (u : ℝ) (hu : u ∈ Icc (0 : ℝ) Dobs) :
      physicalTimeFromNormalized (ampScale A₀ b (k + 1)) entrance u ∈ Icc (0 : ℝ) Hparent := by
    rw [← physicalTime_parent_child_clock hA hb (k := k + 1) (Nat.succ_pos k) entrance u]
    change 0 ≤ entrance + (b * u) / ampScale A₀ b k ∧
      entrance + (b * u) / ampScale A₀ b k ≤ Hparent
    exact ⟨add_nonneg hentrance.1 (div_nonneg (mul_nonneg hb.le hu.1) hAmp.le),
      (add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2 hb.le) hAmp.le)).trans hEnd⟩
  have hh := hobsξ (Hglob := T) (achild := 1 / 16) (aparent := 1 / 16) (d := d)
    (Dchild := Hchild) (Dparent := Hparent) le_rfl hdrift hdR hHchild hHparent
    (k + 1) (k + 1) (Nat.succ_pos k) le_rfl S hS harea X hX 0 exit entrance angle hclock hentrance hmatch
    Y hY hwindow hweighted hcur
  intro u hu
  have htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u) =
      physicalTimeFromNormalized (ampScale A₀ b (k + 1)) entrance u :=
    physicalTime_parent_child_clock hA hb (k := k + 1) (Nat.succ_pos k) entrance u
  rw [htime]
  exact hh u hu

end CircularMaterialTransferProfile
end Euler2D

end
