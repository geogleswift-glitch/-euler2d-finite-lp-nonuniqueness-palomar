module

public import RequestProject.Euler.CircularActualFirstParentHistory
public import RequestProject.Euler.CircularSharpRetardedComparison
public import RequestProject.Euler.CircularCanonicalObservedChildMoment

/-! The true first parent is compared to the ORIGINAL retarded response.
Its equation and physical source errors are constructed from actual
joint controls, and its literal entrance discrepancy is retained. -/

@[expose] public section

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

theorem exists_eventually_actualFirstParent_retarded_comparison
    {b Cb Kw Kcur : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hCb : 0 ≤ Cb) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ C > 0,
      ∀ {s A₀ q T Dobs : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hA : 0 < A₀) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → 0 ≤ Dobs → ∀ᶠ ξ : ℝ in atTop,
        let ρ := Real.exp (-ξ)
        let hρ := Real.exp_pos (-ξ)
        let h := 2 * ρ ^ 6
        ∀ k : ℕ,
        ∀ S : BoundedEulerParticleSystem
          (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
            (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) (k + 1)) T,
        IsFourfoldBoundedEulerParticleSystem S →
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ (Nat.le_succ k) S H Y →
        ∀ entrance angle sObs η : ℝ, 0 ≤ entrance → 0 ≤ η →
        entrance + b * Dobs / ampScale A₀ b k ≤ H →
        (∀ u ∈ Icc (0 : ℝ) Dobs,
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y (b * u)) ≤ Kw * h) →
        (∀ u ∈ Icc (0 : ℝ) Dobs,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y (b * u) k‖ ≤ Kcur * h) →
        (∀ u ∈ Icc (0 : ℝ) Dobs, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ (k + 1) k,
          ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u)) z - torusCenter‖ ≤
            Cb * ρ * radScale ρ ρ k * (1 + b * u)) →
        (∀ u ∈ Icc (0 : ℝ) Dobs,
          let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u);
          ‖momentN (boxedComplexDensity
              (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ (k + 1) (k + 1)) t)) 4 -
            (ampScale A₀ b (k + 1) : ℂ) * (radScale ρ ρ (k + 1) : ℂ) ^ 6 *
              Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b (k + 1) + angle : ℝ) : ℂ)) * I)) *
                P.moment (sObs + u)‖ ≤ ampScale A₀ b (k + 1) * radScale ρ ρ (k + 1) ^ 6 * η) →
        let σ₀ := ampScale A₀ b k * entrance;
        let W := fun u => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b ρ ρ k Y (σ₀ + b * u);
        let θp := entrance * finiteAncestorAngularVelocity A₀ b k;
        let θc := entrance * finiteAncestorAngularVelocity A₀ b (k + 1) + angle;
        ∀ u ∈ Icc (0 : ℝ) Dobs,
          ‖W u - P.shiftedRetardedTransfer b ρ θp θc sObs u‖ ≤
            (‖W 0 - P.shiftedRetardedTransfer b ρ θp θc sObs 0‖ +
              (C * (ρ ^ 8 * (1 + b * Dobs) ^ 8 + ρ ^ 6 * η)) * u) * Real.exp (b * sigma * u) := by
  have hb1 : b ≤ 1 := hb.2.le.trans (by norm_num)
  obtain ⟨C, hC, hjoint⟩ := P.exists_eventually_actualFirstParent_material_forced_equation
    hb.1 hb1 hCb hKw hKcur
  refine ⟨C, hC, ?_⟩
  intro s A₀ q T Dobs _ hs hA hq hqE hT hDobs
  filter_upwards [hjoint (D := b * Dobs) hs hA hq hqE hT (mul_nonneg hb.1.le hDobs)] with ξ hjointξ
  let ρ := Real.exp (-ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  dsimp only
  intro k S hS H hH Y hY entrance angle sObs η hentrance hη hEnd hweighted hcur hparticles hmoment
  let σ₀ := ampScale A₀ b k * entrance
  let W := fun u : ℝ => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b ρ ρ k Y (σ₀ + b * u)
  let θp := entrance * finiteAncestorAngularVelocity A₀ b k
  let θc := entrance * finiteAncestorAngularVelocity A₀ b (k + 1) + angle
  let ε := C * (ρ ^ 8 * (1 + b * Dobs) ^ 8 + ρ ^ 6 * η)
  have hAmp : 0 < ampScale A₀ b k := div_pos hA (pow_pos hb.1 k)
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hclock0 : physicalTimeFromNormalized (ampScale A₀ b k) 0 (σ₀ + b * 0) = entrance := by
    simp only [σ₀, physicalTimeFromNormalized, mul_zero, add_zero, zero_add,
      mul_div_cancel_left₀ entrance hAmp.ne']
  have hphase0 : Complex.exp (4 * (((θp - θc : ℝ) : ℂ)) * I) =
      Complex.exp (-((2 * σ₀ + 4 * angle : ℝ) : ℂ) * I) := by
    have hh := actualAdjacentPhase_from_parent_clock hA hb.1 k entrance σ₀ 0 angle hclock0
    simpa only [θp, θc, mul_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one] using hh
  have hW : ∀ u ∈ Icc (0 : ℝ) Dobs, ∃ E : ℂ, ‖E‖ ≤ ε ∧
      HasDerivAt W (((b : ℂ) * lamStar) * W u +
        (ρ : ℂ) ^ 6 * Kstar * Complex.exp (4 * (((θp - θc : ℝ) : ℂ)) * I) *
          Complex.exp (-((2 * b * u : ℝ) : ℂ) * I) * P.moment (sObs + u) + E) u := by
    intro u hu
    let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u)
    have ht : t ∈ Icc (0 : ℝ) H := by
      change 0 ≤ entrance + (b * u) / ampScale A₀ b k ∧
        entrance + (b * u) / ampScale A₀ b k ≤ H
      exact ⟨add_nonneg hentrance (div_nonneg (mul_nonneg hb.1.le hu.1) hAmp.le),
        (add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2 hb.1.le) hAmp.le)).trans hEnd⟩
    have hclock : physicalTimeFromNormalized (ampScale A₀ b k) 0 (σ₀ + b * u) = t := by
      dsimp only [t, σ₀, physicalTimeFromNormalized]
      rw [add_div, mul_div_cancel_left₀ entrance hAmp.ne']
      simp only [zero_add]
    have heq (j : ℕ) (hj : j ≤ k) :
        canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y (σ₀ + b * u) j =
          canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y (b * u) j :=
      canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.1.ne' ρ ρ le_rfl Y Y
        t entrance (b * u) 0 (σ₀ + b * u) rfl hclock (fun _ => rfl) j hj
    have hnormeq : weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y (σ₀ + b * u)) =
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y (b * u)) :=
      weightedFamilyNorm_congr_prefix h k (fun j => heq j j.isLt.le)
    have hweightedOwn : weightedFamilyNorm h k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y (σ₀ + b * u)) ≤ Kw * h :=
      hnormeq.trans_le (hweighted u hu)
    have hcurOwn : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k 0 Y (σ₀ + b * u) k‖ ≤ Kcur * h := by
      rw [heq k le_rfl]
      exact hcur u hu
    have hparticlesOwn : ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b ρ ρ (k + 1) k,
        ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale ρ ρ k * (1 + b * Dobs) := by
      intro z hz
      have hh := hparticles u hu z hz
      exact hh.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu.2 hb.1.le))
        (mul_nonneg (mul_nonneg hCb hρ.le) (radScale_pos hρ hρ k).le))
    obtain ⟨E, hE, hd⟩ := hjointξ k S hS hH Y hY t ht σ₀ u
      (t * finiteAncestorAngularVelocity A₀ b (k + 1) + angle) hclock
      hweightedOwn hcurOwn hparticlesOwn η hη (P.moment (sObs + u)) (hmoment u hu)
    have hphase := actualAdjacentPhase_from_parent_clock hA hb.1 k t σ₀ u angle hclock
    rw [← hphase0] at hphase
    rw [hphase] at hd
    exact ⟨E, hE, by simpa only [W, mul_assoc] using hd⟩
  have hh := P.dist_shiftedRetardedTransfer_sharp_le_of_forced_equation
    (a := 0) (d := Dobs) hb hε W hW
  simpa only [W, mul_zero, add_zero, sub_zero] using hh

theorem eventually_actualFirstParent_observed_child_moment
    {sObs s A₀ b q T Dobs Cw Ccur Cback η : ℝ} [Fact (1 ≤ ENNReal.ofReal q)]
    (hsObs : sObs ≤ 0) (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hb1 : b ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hT : 0 ≤ T) (hDobs : 0 ≤ Dobs)
    (hCw : 0 ≤ Cw) (hCcur : 0 ≤ Ccur) (hη : 0 < η) :
    ∀ᶠ ξ : ℝ in atTop,
      let ρ := Real.exp (-ξ)
      let hρ := Real.exp_pos (-ξ)
      let h := 2 * ρ ^ 6
      ∀ k : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) (ρ := ρ) hρ hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (ρ := ρ) (q := q) hs hρ hρ) (k + 1)) T,
      IsFourfoldBoundedEulerParticleSystem S →
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (S.forward t) volume volume ∧
        MeasurePreserving (S.backward t) volume volume) →
      ∀ Hchild Hparent : ℝ, 0 ≤ Hchild → 0 ≤ Hparent →
      ∀ X : ℝ → FiniteCircularIndex (k + 1) → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ le_rfl S Hchild X →
      ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b ρ ρ (1 / 16) T hρ hρ (Nat.le_succ k) S Hparent Y →
      ∀ exit entrance angle : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b (k + 1)) 0 exit = entrance →
      entrance ∈ Icc (0 : ℝ) Hchild →
      ‖circularCoRotationCLM γ exit (canonicalPrefixAlignedCurrentCell A₀ b ρ ρ (k + 1) 0 X exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sObs (P.ancient sObs))‖ ≤ Cback * ρ ^ 3 →
      entrance + b * Dobs / ampScale A₀ b k ≤ Hparent →
      (∀ u ∈ Icc (0 : ℝ) Dobs,
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y (b * u)) ≤ Cw * h) →
      (∀ u ∈ Icc (0 : ℝ) Dobs,
        ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b ρ ρ k entrance Y (b * u) k‖ ≤ Ccur * h) →
      ∀ u ∈ Icc (0 : ℝ) Dobs,
        let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u);
        ‖momentN (boxedComplexDensity
            (S.transportedScalar (P.finitePeriodicLabel s A₀ b ρ ρ (k + 1) (k + 1)) t)) 4 -
          (ampScale A₀ b (k + 1) : ℂ) * (radScale ρ ρ (k + 1) : ℂ) ^ 6 *
            Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b (k + 1) + angle : ℝ) : ℂ)) * I)) *
              P.moment (sObs + u)‖ ≤ ampScale A₀ b (k + 1) * radScale ρ ρ (k + 1) ^ 6 * η := by
  let core := cellA / 2
  let δ := cellA / 8
  have hcore : 0 < core := half_pos cellA_pos
  have hδ : 0 < δ := div_pos cellA_pos (by norm_num)
  have hδa : δ ≤ cellA / 4 := by dsimp only [δ]; linarith only [cellA_pos]
  have hcorei (i : Fin 2) : core ≤ 3 * circularContourRadii i / 4 := by
    have hi := (circularContourRadii_bounds i).2.1
    dsimp only [core]
    linarith only [hi, cellA_pos]
  obtain ⟨Cgeo, hCgeo, hobs⟩ := P.exists_eventually_actualCanonical_observed_child_boxed_moment (Cmatch := Cback) hsObs
    hs hA hb hb1 hq hqE hT hcore hcorei (by norm_num : (0 : ℝ) < 2) hCw hCcur hDobs hη hδ hδa
  let d := 2 + 4 * Cgeo * A₀ * T
  have hcat : 0 ≤ Cgeo * A₀ * T := mul_nonneg (mul_nonneg hCgeo.le hA.le) hT
  have hsmall (A ε : ℝ) (hε : 0 < ε) : ∀ᶠ ξ : ℝ in atTop, A * Real.exp (-ξ) ≤ ε := by
    have ht : Tendsto (fun ξ : ℝ => A * Real.exp (-ξ)) atTop (𝓝 0) := by
      simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul A
    exact (ht.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  filter_upwards [hobs, hsmall 1 (b / 2) (half_pos hb), hsmall d (1 / 4) (by norm_num)]
    with ξ hobsξ hρhalf hdR
  simp only [one_mul] at hρhalf
  let ρ := Real.exp (-ξ)
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
