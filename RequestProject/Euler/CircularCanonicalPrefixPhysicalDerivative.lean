module

public import RequestProject.Euler.CircularFinitePrefixMaterialTube
public import RequestProject.Euler.CircularFinitePrefixPhysicalForcing

/-! The actual canonical active-prefix field is the literal full
same-S physical velocity on every active interface. Projection of
the canonical trajectory therefore supplies the original material
cell derivative, without a new path or a forcing-equation hypothesis. -/

@[expose] public section

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actualPrefix_phaseDensity_eq_boxedLabels
    {s A₀ b R ρ c δ : ℝ} (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (W : FiniteCircularIndex k → LittleContourSpace γ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (W p).val) :
    phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (fun p => (W p).val) =
      fun z => ∑ l ∈ Finset.range (k + 1), boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) z := by
  classical
  have hlabel (l : Fin (k + 1)) (z : ℂ) :
      boxedComplexDensity (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) z =
        phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (l, i))
          (fun i => (W (l, i)).val) z := by
    let ll : Fin (N + 1) := ⟨l, l.isLt.trans_le (Nat.succ_le_succ hkN)⟩
    have hlk : (ll : ℕ) ≤ k := Nat.le_of_lt_succ l.isLt
    have hGi (i : Fin 2) : G.contours (ll, i) = (W (l, i)).val := hG (l, i)
    have hh := P.boxed_transported_finitePeriodicLabel_eq_phaseContours
      (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N ll S G.contours t ht
      (G.initial_box ll hlk) (G.current_box ll hlk) (G.images ll hlk) z
    simp only [hGi] at hh
    simp only [ll, finiteCircularInterfaceStrength] at hh ⊢
    exact hh
  funext z
  change (∑ p : FiniteCircularIndex k,
    finiteCircularInterfaceStrength A₀ b p * phaseContourPatchVorticity (W p).val z) = _
  rw [Fintype.sum_prod_type]
  have hsum := Fin.sum_univ_eq_sum_range (fun l : ℕ => boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t) z) (k + 1)
  rw [← hsum]
  exact Finset.sum_congr rfl (fun l _ => (hlabel l z).symm)

theorem actualPrefix_phaseVelocity_eq_labelVelocities
    {s A₀ b R ρ c δ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (W : FiniteCircularIndex k → LittleContourSpace γ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (W p).val) (z : ℂ) :
    velocityC (phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (fun p => (W p).val)) z =
      ∑ l ∈ Finset.range (k + 1), velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N l) t)) z := by
  rw [P.actualPrefix_phaseDensity_eq_boxedLabels hs hR hRmax hρ hρ1 hkN S t ht G W hG]
  unfold velocityC
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  apply integral_finset_sum
  intro l hl
  obtain ⟨hi, hsup, _⟩ := P.boxed_finitePeriodicLabel_bounds hs hA hb hR hRmax hρ hρ1 N l S t
  exact integrable_velocity_integrand hi hsup z

theorem lift_actualPrefix_canonicalField_eq_fullPhysicalVelocity
    {s A₀ b R ρ c δ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {N k : ℕ} (hkN : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (W : FiniteCircularIndex k → LittleContourSpace γ)
    (hG : ∀ p, G.contours (finiteCircularPrefixIndex hkN p) = (W p).val)
    (hphase : IsPhaseAdmissibleLittleContourFamily (finiteCircularReferenceC1 hγ hγ1 R ρ)
      (finiteCircularInterfaceRadius R ρ) W)
    (β : FiniteCircularIndex k → ℝ)
    (hsmall : ∀ p, ‖contourParameterShiftC1 (β p) (W p).val - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤
      finiteCircularInterfaceRadius R ρ p / 4)
    (hlift : ∀ p θ, LittleContourSpace.lift γ
      (S.actualPartialContourForcing (P.finiteInnerInitialLabel s A₀ b R ρ N k) t W p) θ =
        S.physicalLabelComplexField (P.finiteInnerInitialLabel s A₀ b R ρ N k) t (LittleContourSpace.lift γ (W p) θ))
    (p : FiniteCircularIndex k) (θ : ℝ) :
    LittleContourSpace.lift γ
      (S.actualPartialPhaseField (P.finiteInnerInitialLabel s A₀ b R ρ N k) hγ hγ1
        (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
        (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceStrength A₀ b) t W p) θ =
      velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t)
        (LittleContourSpace.lift γ (W p) θ) +
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (LittleContourSpace.lift γ (W p) θ))) := by
  change LittleContourSpace.lift γ (finiteContourPhaseFieldTotal hγ hγ1
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
    (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceStrength A₀ b) W p) θ +
    LittleContourSpace.lift γ (S.actualPartialContourForcing (P.finiteInnerInitialLabel s A₀ b R ρ N k) t W p) θ = _
  rw [lift_finiteContourPhaseFieldTotal hγ hγ1 _ _ _ _ _ W hphase p θ, hlift p θ]
  have hboundary : contourBoundaryField (finiteCircularInterfaceStrength A₀ b)
      (fun p => LittleContourSpace.lift γ (W p)) p θ =
      velocityC (phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b)
        (fun p => (W p).val)) (LittleContourSpace.lift γ (W p) θ) :=
    contourBoundaryField_eq_phase_actual_velocity (finiteCircularInterfaceStrength A₀ b)
      (fun p => (W p).val) (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) β hsmall p θ
  rw [hboundary]
  rw [S.physicalLabelComplexField_eq, P.physicalComplexSource_finiteInnerInitialLabel_eq,
    P.actualPrefix_phaseVelocity_eq_labelVelocities hs hA hb hR hRmax hρ hρ1 hkN S t ht G W hG,
    P.velocityC_physicalFiniteDensity_eq_outer_add_cluster hs hA hb hR hRmax hρ hρ1 N k hkN S t]
  abel

end CircularMaterialTransferProfile
end Euler2D

end
