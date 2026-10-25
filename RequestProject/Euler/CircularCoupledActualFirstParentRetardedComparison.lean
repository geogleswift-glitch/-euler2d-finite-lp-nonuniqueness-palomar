module

public import RequestProject.Euler.CircularActualFirstParentComparison
public import RequestProject.Euler.CircularCoupledActualJointMaterialEquation

/-! Compare the SAME actual first-parent growing coordinate to the
ORIGINAL shifted retarded response with R=rho^10, A0=cA*(1+xi).
The actual entrance discrepancy and literal physical child moment
error remain explicit; no independent scalar solution is substituted. -/

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

theorem exists_eventually_actualFirstParent_coupled_retarded_comparison
    {b Cb Kw Kcur : ℝ} (hb : b ∈ Ioo (0 : ℝ) (1 / 4))
    (hCb : 0 ≤ Cb) (hKw : 0 ≤ Kw) (hKcur : 0 ≤ Kcur) :
    ∃ C > 0,
      ∀ {s cA q T Dobs : ℝ}, ∀ [Fact (1 ≤ ENNReal.ofReal q)],
      ∀ (hs : s ≤ 0) (hcA : 0 < cA) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      0 ≤ T → 0 ≤ Dobs → ∀ᶠ ξ : ℝ in atTop,
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
        ∀ {H : ℝ}, 0 ≤ H → ∀ Y : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
        P.ActualCanonicalPrefixTrajectory s A₀ b R ρ (1 / 16) T hR hρ (Nat.le_succ k) S H Y →
        ∀ entrance angle sObs η : ℝ, 0 ≤ entrance → 0 ≤ η →
        entrance + b * Dobs / ampScale A₀ b k ≤ H →
        (∀ u ∈ Icc (0 : ℝ) Dobs,
          weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u)) ≤ Kw * h) →
        (∀ u ∈ Icc (0 : ℝ) Dobs,
          ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u) k‖ ≤ Kcur * h) →
        (∀ u ∈ Icc (0 : ℝ) Dobs, ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k,
          ‖S.forward (physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u)) z - torusCenter‖ ≤
            Cb * ρ * radScale R ρ k * (1 + b * u)) →
        (∀ u ∈ Icc (0 : ℝ) Dobs,
          let t := physicalTimeFromNormalized (ampScale A₀ b k) entrance (b * u);
          ‖momentN (boxedComplexDensity
              (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ (k + 1) (k + 1)) t)) 4 -
            (ampScale A₀ b (k + 1) : ℂ) * (radScale R ρ (k + 1) : ℂ) ^ 6 *
              Complex.exp (-(4 * (((t * finiteAncestorAngularVelocity A₀ b (k + 1) + angle : ℝ) : ℂ)) * I)) *
                P.moment (sObs + u)‖ ≤ ampScale A₀ b (k + 1) * radScale R ρ (k + 1) ^ 6 * η) →
        let σ₀ := ampScale A₀ b k * entrance;
        let W := fun u => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (σ₀ + b * u);
        let θp := entrance * finiteAncestorAngularVelocity A₀ b k;
        let θc := entrance * finiteAncestorAngularVelocity A₀ b (k + 1) + angle;
        ∀ u ∈ Icc (0 : ℝ) Dobs,
          ‖W u - P.shiftedRetardedTransfer b ρ θp θc sObs u‖ ≤
            (‖W 0 - P.shiftedRetardedTransfer b ρ θp θc sObs 0‖ +
              (C * (ρ ^ 8 * (1 + b * Dobs) ^ 8 + ρ ^ 6 * η)) * u) * Real.exp (b * sigma * u) := by
  have hb1 : b ≤ 1 := hb.2.le.trans (by norm_num)
  obtain ⟨C, hC, hjoint⟩ := P.exists_eventually_actualFirstParent_coupled_material_forced_equation
    hb.1 hb1 hCb hKw hKcur
  refine ⟨C, hC, ?_⟩
  intro s cA q T Dobs _ hs hcA hq hqE hT hDobs
  filter_upwards [hjoint (D := b * Dobs) hs hcA hq hqE hT (mul_nonneg hb.1.le hDobs), eventually_ge_atTop (0 : ℝ)] with ξ hjointξ hξ
  let ρ := Real.exp (-ξ)
  let R := ρ ^ 10
  let A₀ := cA * (1 + ξ)
  let h := 2 * ρ ^ 6
  have hρ : 0 < ρ := Real.exp_pos (-ξ)
  have hR : 0 < R := pow_pos hρ 10
  have hA : 0 < A₀ := mul_pos hcA (by linarith only [hξ])
  dsimp only
  intro k S hS H hH Y hY entrance angle sObs η hentrance hη hEnd hweighted hcur hparticles hmoment
  let σ₀ := ampScale A₀ b k * entrance
  let W := fun u : ℝ => canonicalPrefixMaterialGrowingCoordinate hγ hγ1 A₀ b R ρ k Y (σ₀ + b * u)
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
        canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (σ₀ + b * u) j =
          canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u) j :=
      canonicalPrefixStageDeviation_crossPrefix_eq hγ hγ1 hA.ne' hb.1.ne' R ρ le_rfl Y Y
        t entrance (b * u) 0 (σ₀ + b * u) rfl hclock (fun _ => rfl) j hj
    have hnormeq : weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (σ₀ + b * u)) =
        weightedFamilyNorm h k (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k entrance Y (b * u)) :=
      weightedFamilyNorm_congr_prefix h k (fun j => heq j j.isLt.le)
    have hweightedOwn : weightedFamilyNorm h k
        (canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (σ₀ + b * u)) ≤ Kw * h :=
      hnormeq.trans_le (hweighted u hu)
    have hcurOwn : ‖canonicalPrefixStageDeviation hγ hγ1 A₀ b R ρ k 0 Y (σ₀ + b * u) k‖ ≤ Kcur * h := by
      rw [heq k le_rfl]
      exact hcur u hu
    have hparticlesOwn : ∀ z ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ (k + 1) k,
        ‖S.forward t z - torusCenter‖ ≤ Cb * ρ * radScale R ρ k * (1 + b * Dobs) := by
      intro z hz
      have hh := hparticles u hu z hz
      exact hh.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hu.2 hb.1.le))
        (mul_nonneg (mul_nonneg hCb hρ.le) (radScale_pos hR hρ k).le))
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


end CircularMaterialTransferProfile
end Euler2D

end
