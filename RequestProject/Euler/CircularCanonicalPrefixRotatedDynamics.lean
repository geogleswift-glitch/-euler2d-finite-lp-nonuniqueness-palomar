module

public import RequestProject.Euler.CircularCanonicalPrefixCoreGeometry
public import RequestProject.Euler.CircularCanonicalPrefixRetardedAlignment

/-! Fixed-stage rotating dynamics of the original canonical X. Its
Banach derivative, physical lift, isolated domain and ancestor-core
geometry are all derived from the actual canonical validity domain. -/

@[expose] public section

set_option maxHeartbeats 14000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualCanonicalPrefix_sameGauge_hasDerivAt
    {s A₀ b R ρ c δ a Hglob D : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρcore : (5 / 4 : ℝ) * ρ ≤ cellA)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (hglobT : Hglob ≤ T)
    (hwf : P.finiteInitialPeriodicDensity s A₀ b R ρ N =ᵐ[μT] (f : R2 → ℝ))
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (hX : IsBanachTimeDomainTrajectoryOn
      (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b))
      (S.actualPartialPhaseDomain (P.finiteInnerInitialLabel s A₀ b R ρ N k)
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ) a Hglob)
      (fun p => finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (finiteCircularPrefixIndex hkN p)) D X)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (X t p).val)
    (j : Fin (k + 1)) (Q : Fin 2 → LittleContourSpace γ)
    (hQ : ∀ i θ, LittleContourSpace.lift γ (Q i) θ =
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k ((Nat.le_of_lt_succ j.isLt).trans hkN) S t
        (LittleContourSpace.lift γ (X t (j, i)) θ))
    (aTime τ : ℝ) (htime : physicalTimeFromNormalized (ampScale A₀ b k) aTime τ = t) :
    let A := ampScale A₀ b k
    let r := radScale R ρ j
    let Ω := finiteAncestorAngularVelocity A₀ b j
    let y := fun u => canonicalPrefixRotatedCell A₀ b R ρ k aTime X u j
    let p := rigidRotationGauge (Ω / A) 0 τ • ((A * r)⁻¹ • Q)
    HasDerivAt y ((b ^ (k - (j : ℕ))) • circularBanachField hγ hγ1 (y τ) + p) τ ∧
      ‖p‖ = ‖Q‖ / (A * r) := by
  let z : ℝ → Fin 2 → LittleContourSpace γ := fun u i => X u (j, i)
  let W : Fin 2 → LittleContourSpace γ := (radScale R ρ j)⁻¹ • z t
  let F : ℝ → (FiniteCircularIndex k → LittleContourSpace γ) → FiniteCircularIndex k → LittleContourSpace γ :=
    S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
    (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceStrength A₀ b)
  let Dcell : Fin 2 → LittleContourSpace γ := fun i => F t (X t) (j, i)
  have hdcell := P.actualCanonicalPrefix_cell_hasDerivAt_fullPhysical hs hA.le hb hR hRmax hρ hρ1
    hkN S hglobT X hX t ht G hG j
  have hzd : HasDerivAt z Dcell t := hdcell.1
  have hrj : 0 < radScale R ρ j := radScale_pos hR hρ j
  have hzt : z t = radScale R ρ j • W := by
    dsimp only [W]
    rw [smul_smul, mul_inv_cancel₀ hrj.ne', one_smul]
  have hlift (i : Fin 2) (θ : ℝ) : LittleContourSpace.lift γ (X t (j, i)) θ =
      radScale R ρ j • LittleContourSpace.lift γ (W i) θ := by
    have hh := congrArg (fun V : Fin 2 → LittleContourSpace γ => LittleContourSpace.lift γ (V i) θ) hzt
    exact hh
  have hmem := hX.mem t ht
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, hmem.1.2.trans hglobT⟩
  have hW : W ∈ circularQuarterPhaseDomain hγ hγ1 :=
    normalizedFiniteCircularCell_mem_quarterPhaseDomain hγ hγ1 hR hρ (X t) hmem.2.1 hmem.2.2.2.1 j
  have hscale (i : Fin 2) : G.contours
      (⟨j, Nat.lt_succ_of_le ((Nat.le_of_lt_succ j.isLt).trans hkN)⟩, i) = radScale R ρ j • (W i).val := by
    have hh := hG (j, i)
    exact hh.trans (congrArg Subtype.val (congrFun hzt i))
  have hD : ∀ i θ, LittleContourSpace.lift γ (Dcell i) θ =
      velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ) +
      planeComplexEquiv (S.correctionLabelField t
        (complexTorusPoint (radScale R ρ j • LittleContourSpace.lift γ (W i) θ))) := by
    intro i θ
    simpa only [hlift] using hdcell.2 i θ
  have hQ' : ∀ i θ, LittleContourSpace.lift γ (Q i) θ =
      P.finitePrefixOffSelfPhysicalField s A₀ b R ρ N j k ((Nat.le_of_lt_succ j.isLt).trans hkN) S t
        (radScale R ρ j • LittleContourSpace.lift γ (W i) θ) := by
    intro i θ
    simpa only [hlift] using hQ i θ
  have hx : ∀ i θ, ∀ l : Fin (j : ℕ), ‖radScale R ρ j • LittleContourSpace.lift γ (W i) θ‖ ≤
      cellA * radScale R ρ l := by
    intro i θ l
    rw [← hlift]
    exact canonicalPrefix_cell_in_ancestor_core hγ hγ1 hR hρ hρ1 hρcore (X t) hmem.2.2.2.1 j i θ l
  exact P.hasDerivAt_actualPrefix_sameGauge_currentClock hs hA hb hR hRmax hρ hρ1
    N j k (Nat.le_of_lt_succ j.isLt) hkN S hwf G.contours t htT W hW hscale
    (G.initial_box _ (Nat.le_of_lt_succ j.isLt)) (G.current_box _ (Nat.le_of_lt_succ j.isLt)) (G.images _ (Nat.le_of_lt_succ j.isLt))
    hx Dcell Q hD hQ' z hzd hzt aTime τ htime

end CircularMaterialTransferProfile
end Euler2D

end

