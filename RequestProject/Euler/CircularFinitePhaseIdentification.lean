module

public import RequestProject.Euler.FinitePhaseTorusDensityIdentification
public import RequestProject.Euler.CircularFiniteContourPhysicalBounds

/-! The actual finite circular Euler family is identified with its
material contour path across phase charts. The initial ancient sample,
the original torus system and the literal periodic density are retained. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex Set Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteEuler_phaseContour_agreement {s A₀ b R ρ q T D : ℝ}
    [Fact (1 ≤ ENNReal.ofReal q)] (hs : s ≤ 0)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 < q) (hqE : 2 ≤ ENNReal.ofReal q) (hD : 0 ≤ D) (hDT : D ≤ T)
    (hRbox : (5 / 4) * R < 1) (N : ℕ)
    (S : BoundedEulerParticleSystem
      (finiteBaseCurlL2 (A₀ := A₀) (b := b) hR hρ hq hqE
        (P.finiteBaseLp (A₀ := A₀) (b := b) (q := q) hs hR hρ) N) T)
    (Z : ℝ → FiniteCircularIndex N → ContourC1Space γ)
    (hZ0 : Z 0 = fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val)
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : FiniteCircularIndex N → ℝ, ∀ p,
      ‖contourParameterShiftC1 (b p) (Z t p) - finiteCircularReferenceC1 hγ hγ1 R ρ p‖ <
        finiteCircularInterfaceRadius R ρ p / 4)
    (hZc : ∀ p, ContinuousOn (fun t => Z t p) (Icc (0 : ℝ) D))
    (hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ p θ,
      HasDerivAt (fun u => ContourC1Space.lift γ (Z u p) θ)
        (contourC1BoundaryField (finiteCircularInterfaceStrength A₀ b) (Z t) p θ +
          planeComplexEquiv (S.correctionLabelField t
            (complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)))) t)
    (hactive : ∀ t ∈ Icc (0 : ℝ) D, ∀ a, ‖a - torusCenter‖ ≤ (5 / 4) * R →
      ∀ y, P.finiteInitialPlanarDensity s A₀ b R ρ N (y - torusCenter) ≠ 0 →
        ‖S.forward t a - S.forward t y‖ ≤ 1 / 2) :
    ∀ t ∈ Icc (0 : ℝ) D,
      (∀ p θ, S.forward t (complexTorusPoint (ContourC1Space.lift γ (Z 0 p) θ)) =
        complexTorusPoint (ContourC1Space.lift γ (Z t p) θ)) ∧
      (∀ p, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z 0 p))) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z t p))) ∧
      ∀ x ∈ torusBox, S.transportedScalar (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t x =
        phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z t)
          (centeredComplexHomeomorph.symm x) := by
  let w : R2 → ℝ := fun x => P.finiteInitialPlanarDensity s A₀ b R ρ N (x - torusCenter)
  have hωeq (x : R2) : phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b) (Z 0)
      (centeredComplexHomeomorph.symm x) = w x := by
    rw [hZ0, P.finiteCircularInitial_density_eq hR hρ N,
      centeredComplexHomeomorph_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hwf := (P.finiteBaseCurlL2_ae_density (A₀ := A₀) (b := b) hs hR hρ hq hqE N).symm
  let A : Set R2 := closedBall torusCenter ((5 / 4) * R)
  have hAbox : A ⊆ torusBox := by
    intro x hx
    exact norm_sub_center_lt_one_mem_box ((mem_closedBall_iff_norm.mp hx).trans_lt hRbox)
  have hdomain (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (p : FiniteCircularIndex N) {z : ℂ}
      (hz : z ∈ contourRadialFill (ContourC1Space.lift γ (Z t p))) : complexTorusPoint z ∈ A := by
    obtain ⟨β, hβ⟩ := hphase t ht
    apply mem_closedBall_iff_norm.mpr
    rw [complexTorusPoint_sub_center_norm]
    have hn := norm_lt_of_mem_contourRadialFill_of_shift (Z t p)
      (finiteCircularReferenceC1 hγ hγ1 R ρ p) (finiteCircularInterfaceRadius_pos hR hρ p)
      (lift_finiteCircularReferenceC1 hγ hγ1 R ρ p) (β p) (hβ p).le hz
    have hr := finiteCircularInterfaceRadius_le hR hρ hρ1 p
    linarith
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (p : FiniteCircularIndex N) (θ : ℝ) :
      complexTorusPoint (ContourC1Space.lift γ (Z t p) θ) ∈ A := by
    obtain ⟨β, hβ⟩ := hphase t ht
    have hn := finiteCircular_contour_boundary_radius hγ hγ1 hR hρ hρ1
      (fun j => contourParameterShiftC1 (β j) (Z t j)) (fun j => (hβ j).le) p (θ - β p)
    apply mem_closedBall_iff_norm.mpr
    simpa only [lift_contourParameterShiftC1, sub_add_cancel] using hn
  have hagree := S.finitePhase_actualCorrection_agreement
    (finiteCircularInterfaceStrength A₀ b) Z (finiteCircularReferenceC1 hγ hγ1 R ρ)
    (finiteCircularInterfaceRadius R ρ) (finiteCircularInterfaceRadius_pos hR hρ)
    (lift_finiteCircularReferenceC1 hγ hγ1 R ρ) hD hDT hZc hphase hmat w
    (fun x => (hωeq x).symm) hwf hAbox
    (fun p z hz => hdomain 0 ⟨le_rfl, hD⟩ p hz) (hboundary 0 ⟨le_rfl, hD⟩)
    (fun t ht a ha => ae_of_all _ fun y hy => hactive t ht a (mem_closedBall_iff_norm.mp ha) y hy)
  intro t ht
  refine ⟨(hagree t ht).1, (hagree t ht).2, ?_⟩
  intro x hx
  apply S.transportedScalar_finitePhase_eq_of_domain_images
    (finiteCircularInterfaceStrength A₀ b) (Z 0) (Z t) _
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
