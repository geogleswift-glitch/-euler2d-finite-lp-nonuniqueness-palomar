module

public import RequestProject.Euler.CircularFiniteContourPhysicalBounds
public import RequestProject.Euler.CircularFiniteContourLocalFlow
public import RequestProject.Euler.CircularFiniteActiveWindow

/-! The actual finite circular density and the same original torus Euler
system agree with its material contour evolution. Both the boundary and
the enclosed regions are identified, then wrapped density transport is
identified literally on the fundamental box. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

local instance (priority := 2000) circularIdentificationLittle_group (γ : ℝ≥0) :
    NormedAddCommGroup (LittleContourSpace γ) := Submodule.normedAddCommGroup (LittleContourSpace γ)
local instance (priority := 2000) circularIdentificationLittle_space (γ : ℝ≥0) :
    NormedSpace ℝ (LittleContourSpace γ) := Submodule.normedSpace (LittleContourSpace γ)
local instance (priority := 2000) circularIdentificationC1_group (γ : ℝ≥0) :
    NormedAddCommGroup (ContourC1Space γ) := Submodule.normedAddCommGroup (contourC1GraphSubmodule γ)

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteEuler_contour_agreement {s A₀ b R ρ q T D : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hD : 0 ≤ D) (hDT : D ≤ T)
    (hRbox : (5 / 4) * R < 1) (N : ℕ)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (Z : ℝ → FiniteCircularIndex N → ContourC1Space γ)
    (hZ0 : Z 0 = fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ p,
      ‖Z t p - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ finiteCircularInterfaceRadius R ρ p / 4)
    (hZc : ∀ p, ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) D))
    (hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
      HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
        (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)))) t)
    (hactive : ∀ t ∈ Icc (0 : ℝ) D, ∀ a, ‖a - torusCenter‖ ≤ (5 / 4) * R →
      ∀ y, P.finiteInitialPlanarDensity s A₀ b R ρ N (y - torusCenter) ≠ 0 →
        ‖S.forward t a - S.forward t y‖ ≤ 1 / 2) :
    ∀ t (ht : t ∈ Icc (0 : ℝ) D),
      (∀ p θ, S.forward t (complexTorusPoint (ContourC1Space.lift γ (Z 0 p) θ)) =
        complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)) ∧
      (∀ p, S.forward t '' (complexTorusPoint '' contourC1EnclosedDomain (Z 0 p)
          (finiteCircularReferenceC1 hγ hγ1 R ρ p) (finiteCircularInterfaceRadius_pos hR hρ p)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p) (hsmall 0 ⟨le_rfl, hD⟩ p)) =
        complexTorusPoint '' contourC1EnclosedDomain (Z t p)
          (finiteCircularReferenceC1 hγ hγ1 R ρ p) (finiteCircularInterfaceRadius_pos hR hρ p)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p) (hsmall t ht p)) ∧
      ∀ x ∈ torusBox, S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
        finiteContourC1PatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z t)
          (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
          (finiteCircularInterfaceRadius_pos hR hρ)
          (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (hsmall t ht)
          (centeredComplexHomeomorph.symm x) := by
  let w : R2 → ℝ := fun x => P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter)
  have hωeq (x : R2) : finiteContourC1PatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z 0)
      (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
      (finiteCircularInterfaceRadius_pos hR hρ)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) (hsmall 0 ⟨le_rfl, hD⟩)
      (centeredComplexHomeomorph.symm x) = w x := by
    have hstart : ∀ p : FiniteCircularIndex N,
        ‖(finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val -
          finiteCircularReferenceC1 hγ hγ1 R ρ p‖ ≤ finiteCircularInterfaceRadius R ρ p / 4 := by
      simpa only [hZ0] using hsmall 0 ⟨le_rfl, hD⟩
    simpa only [hZ0, w] using P.finiteCircularInitial_C1_density_eq hR hρ N hstart x
  have hwf := (P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N).symm
  let A : Set R2 := closedBall torusCenter ((5 / 4) * R)
  have hAbox : A ⊆ torusBox := by
    intro x hx
    exact norm_sub_center_lt_one_mem_box ((mem_closedBall_iff_norm.mp hx).trans_lt hRbox)
  have hdomain (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (p : FiniteCircularIndex N) {z : ℂ}
      (hz : z ∈ contourC1EnclosedDomain (Z t p) (finiteCircularReferenceC1 hγ hγ1 R ρ p)
        (finiteCircularInterfaceRadius_pos hR hρ p) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p)
        (hsmall t ht p)) : complexTorusPoint z ∈ A := by
    exact mem_closedBall_iff_norm.mpr
      (finiteCircular_contour_domain_radius hγ hγ1 hR hρ hρ1 (Z t) (hsmall t ht) p hz)
  have hagree := S.finiteContour_actualCorrection_agreement
    (finiteCircularInterfaceStrength A₀ b) Z (finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
    (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hD hDT hsmall hZc hmat w
    (fun x => by
      rw [finiteContourPatchVorticityOnInterval_of_mem
        (finiteCircularInterfaceStrength A₀ b) Z (finiteCircularReferenceC1 hγ hγ1 R ρ)
        (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
        (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hsmall ⟨le_rfl, hD⟩]
      exact (hωeq x).symm) hwf hAbox
    (fun p z hz => hdomain 0 ⟨le_rfl, hD⟩ p hz)
    (fun p θ => mem_closedBall_iff_norm.mpr
      (finiteCircular_contour_boundary_radius hγ hγ1 hR hρ hρ1 (Z 0) (hsmall 0 ⟨le_rfl, hD⟩) p θ))
    (fun t ht a ha => ae_of_all _ fun y hy => hactive t ht a (mem_closedBall_iff_norm.mp ha) y hy)
  intro t ht
  refine ⟨(hagree t ht).1, (hagree t ht).2, ?_⟩
  intro x hx
  apply S.transportedScalar_finiteContour_eq_of_domain_images
    (finiteCircularInterfaceStrength A₀ b) (Z 0) (Z t)
    (finiteCircularReferenceC1 hγ hγ1 R ρ) (finiteCircularInterfaceRadius R ρ)
    (finiteCircularInterfaceRadius_pos hR hρ) (lift_finiteCircularReferenceC1 hγ hγ1 R ρ)
    (hsmall 0 ⟨le_rfl, hD⟩) (hsmall t ht) _
    (fun y hy => (P.finiteInitialPeriodicDensity_eq_on_box hs hR hRmax hρ hρ1 N hy).trans
      (hωeq y).symm) t ⟨ht.1, ht.2.trans hDT⟩
    (fun p z hz => by
      obtain ⟨u, hu, rfl⟩ := hz
      exact hAbox (hdomain 0 ⟨le_rfl, hD⟩ p hu))
    (fun p z hz => by
      obtain ⟨u, hu, rfl⟩ := hz
      exact hAbox (hdomain t ht p hu)) (hagree t ht).2 hx

end CircularMaterialTransferProfile
end Euler2D

end
