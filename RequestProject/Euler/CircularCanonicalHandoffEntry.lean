module

public import RequestProject.Euler.CircularCanonicalPrefixMaterialImages
public import RequestProject.Euler.CircularCanonicalHandoffAlignment
public import RequestProject.Euler.CircularCanonicalCurrentCoordinates
public import RequestProject.Euler.ContourPhaseComplexScale

/-! Recover the literal physical entry contours from the fixed
canonical handoff alignment. Its coframe is the actual ancestor
angle plus the observed section angle. Domain images and section
closeness are derived on the SAME original canonical trajectory. -/

@[expose] public section

set_option maxHeartbeats 16000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local instance 2000] rigidGaugeLittle_group rigidGaugeLittle_space rigidGaugeFamily_tower
attribute [local instance] LittleContourSpace.complexScalarNormedSpace LittleContourSpace.complexScalarTower
attribute [local instance 2000] valueScalarC1_group valueScalarC1_space
attribute [local instance] ContourC1Space.complexScalarNormedSpace ContourC1Space.complexScalarTower

theorem lift_circularCanonicalHandoffAlignment {γ : ℝ≥0}
    (s angle exit : ℝ) (Y : Fin 2 → LittleContourSpace γ) (i : Fin 2) (u : ℝ) :
    LittleContourSpace.lift γ (circularCanonicalHandoffAlignmentCLM γ s angle exit Y i) u =
      Complex.exp ((-angle : ℂ) * I) * LittleContourSpace.lift γ (Y i)
        (u + circularContourAngularVelocities i * s + angle - circularContourAngularVelocities i * exit) := by
  change LittleContourSpace.lift γ
    (contourParameterShiftLittleCLM γ (-circularContourAngularVelocities i * (-s))
      (contourRotationLittleCLM γ (-angle)
        (contourParameterShiftLittleCLM γ (-circularContourAngularVelocities i * exit) (Y i)))) u = _
  rw [lift_contourParameterShiftLittleCLM, lift_contourRotationLittleCLM]
  simp only [rotShift, Complex.ofReal_neg]
  rw [lift_contourParameterShiftLittleCLM]
  congr 2
  ring

theorem canonicalPrefix_handoff_entry_contours {γ : ℝ≥0}
    {A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (k : ℕ)
    (X : ℝ → FiniteCircularIndex k → LittleContourSpace γ)
    (entrance exit t sCanon angle : ℝ)
    (htime : physicalTimeFromNormalized (ampScale A₀ b k) entrance exit = t) :
    let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
    let W := circularCanonicalHandoffAlignmentCLM γ sCanon angle exit (y exit)
    let θ := t * finiteAncestorAngularVelocity A₀ b k + angle
    let β := fun i : Fin 2 => circularContourAngularVelocities i *
      (ampScale A₀ b k * entrance + exit - sCanon) - angle
    ∀ i, (X t (Fin.last k, i)).val = radScale R ρ k •
      ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I)) (contourParameterShiftC1 (β i) (W i).val) := by
  dsimp only
  intro i
  apply ContourC1Space.ext
  intro x
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  let Y := canonicalPrefixAbsoluteCell A₀ b R ρ k entrance X exit (Fin.last k)
  have hraw := congrArg (fun Z : Fin 2 → LittleContourSpace γ => LittleContourSpace.lift γ (Z i) u)
    (canonicalPrefixAbsoluteCell_raw (A₀ := A₀) (b := b) hR hρ k entrance exit X (Fin.last k))
  rw [htime] at hraw
  change radScale R ρ k •
    (Complex.exp (((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I) *
      LittleContourSpace.lift γ (Y i) u) = LittleContourSpace.lift γ (X t (Fin.last k, i)) u at hraw
  change LittleContourSpace.lift γ (X t (Fin.last k, i)) u =
    radScale R ρ k • (Complex.exp (((t * finiteAncestorAngularVelocity A₀ b k + angle : ℝ) : ℂ) * I) *
      LittleContourSpace.lift γ
        (circularCanonicalHandoffAlignmentCLM γ sCanon angle exit
          (canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X exit) i)
        (u + (circularContourAngularVelocities i *
          (ampScale A₀ b k * entrance + exit - sCanon) - angle)))
  rw [lift_circularCanonicalHandoffAlignment]
  change LittleContourSpace.lift γ (X t (Fin.last k, i)) u =
    radScale R ρ k • (Complex.exp (((t * finiteAncestorAngularVelocity A₀ b k + angle : ℝ) : ℂ) * I) *
      (Complex.exp ((-angle : ℂ) * I) * LittleContourSpace.lift γ
        (contourParameterShiftLittleCLM γ (circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance) i) (Y i))
        ((u + (circularContourAngularVelocities i *
          (ampScale A₀ b k * entrance + exit - sCanon) - angle)) +
            circularContourAngularVelocities i * sCanon + angle - circularContourAngularVelocities i * exit)))
  rw [lift_contourParameterShiftLittleCLM]
  have harg : ((u + (circularContourAngularVelocities i *
      (ampScale A₀ b k * entrance + exit - sCanon) - angle)) +
        circularContourAngularVelocities i * sCanon + angle - circularContourAngularVelocities i * exit) +
      circularRetardedMaterialShift 0 (ampScale A₀ b k * entrance) i = u := by
    unfold circularRetardedMaterialShift
    ring
  rw [harg, ← mul_assoc, ← Complex.exp_add]
  have hangle : (((t * finiteAncestorAngularVelocity A₀ b k + angle : ℝ) : ℂ) * I) +
      (-angle : ℂ) * I = ((t * finiteAncestorAngularVelocity A₀ b k : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hangle]
  exact hraw.symm

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem exists_uniform_actualCanonical_handoff_entry :
    ∃ C : ℝ, 0 < C ∧ ∀ {s A₀ b R ρ q T Hglob c : ℝ},
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
        (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρb : ρ < b) (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q),
      Hglob ≤ T → 5 / 4 + (C * A₀ / (1 - ρ / b)) * Hglob < c → c * R ≤ 1 / 4 →
      ∀ N : ℕ,
      ∀ S : BoundedEulerParticleSystem
        (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
          (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T,
      ∀ {k : ℕ} (hkN : k ≤ N) {a D : ℝ}, 0 ≤ D →
      ∀ X : ℝ → FiniteCircularIndex k → LittleContourSpace γ,
      P.ActualCanonicalPrefixTrajectory s A₀ b R ρ a Hglob hR hρ hkN S D X →
      ∀ t ∈ Icc (0 : ℝ) D, ∀ entrance exit sCanon angle : ℝ,
      physicalTimeFromNormalized (ampScale A₀ b k) entrance exit = t →
      let y := canonicalPrefixAlignedCurrentCell A₀ b R ρ k entrance X
      let W := circularCanonicalHandoffAlignmentCLM γ sCanon angle exit (y exit)
      let θ := t * finiteAncestorAngularVelocity A₀ b k + angle
      let β := fun i : Fin 2 => circularContourAngularVelocities i *
        (ampScale A₀ b k * entrance + exit - sCanon) - angle
      (∀ i, (X t (Fin.last k, i)).val = radScale R ρ k •
        ContourC1Space.complexScale (Complex.exp ((θ : ℂ) * I))
          (contourParameterShiftC1 (β i) (W i).val)) ∧
      (∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (LittleContourSpace.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
          (⟨k, Nat.lt_succ_of_le hkN⟩, i)))) =
            complexTorusPoint '' contourRadialFill (LittleContourSpace.lift γ (X t (Fin.last k, i)))) ∧
      ‖W - P.ancient sCanon‖ = ‖circularCoRotationCLM γ exit (y exit) -
        contourRotationFamilyLittleCLM γ angle (circularCoRotationCLM γ sCanon (P.ancient sCanon))‖ := by
  obtain ⟨C, hC, himages⟩ := P.exists_uniform_actualCanonical_prefix_material_images
  refine ⟨C, hC, ?_⟩
  intro s A₀ b R ρ q T Hglob c _ hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR
    N S k hkN a D hD X hX t ht entrance exit sCanon angle htime
  dsimp only
  refine ⟨canonicalPrefix_handoff_entry_contours hR hρ k X entrance exit t sCanon angle htime, ?_, ?_⟩
  · intro i
    exact himages hs hA hb hR hRmax hρ hρ1 hρb hq hqE hglobT hc hcR N S hkN hD X hX t ht (Fin.last k, i)
  · exact circularCanonicalHandoffAlignment_section_error sCanon angle exit _ _

end CircularMaterialTransferProfile
end Euler2D

end
