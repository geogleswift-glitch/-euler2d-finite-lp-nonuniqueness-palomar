module

public import RequestProject.Euler.CircularFinitePhaseIdentification
public import RequestProject.Euler.CircularFiniteLabelTransport

/-! Each individual original finite label, including the ancient inner
base, is the two-interface physical density of its actual transported
domains. The per-interface images are supplied by the proved material
identification; the full-density identity is not used to infer labels. -/

@[expose] public section

set_option maxHeartbeats 3500000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteCircularInitial_label_density_eq {s A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) (j : Fin (N + 1)) (x : ℂ) :
    phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
      (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) x =
      P.finitePlanarLabel s A₀ b R ρ N j (complexPhysicalPlane x) := by
  have hr (k : ℕ) : 0 < radScale R ρ k := mul_pos hR (pow_pos hρ k)
  by_cases hj : (j : ℕ) = N
  · rw [finitePlanarLabel, if_pos hj]
    have he : phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) x =
        ampScale A₀ b N * circularPhasePatchVorticity (P.ancient s) ((radScale R ρ N)⁻¹ • x) := by
      simpa only [phaseFiniteContourPatchVorticity, circularPhasePatchVorticity,
        finiteCircularInterfaceStrength, finiteCircularInitialContours, hj, if_pos rfl,
        ite_true, Submodule.coe_smul] using
        phaseFiniteContourPatchVorticity_scale circularContourStrengths
          (fun i => (P.ancient s i).val) (ampScale A₀ b N) (hr N).ne' x
    rw [he]
    simp only [finiteBaseDensity, circularPhasePatchPlanarVorticity, map_smul,
      LinearIsometryEquiv.symm_apply_apply]
  · rw [finitePlanarLabel, if_neg hj]
    have he : phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) x =
        ampScale A₀ b j * circularPhasePatchVorticity (littleCircularReference hγ hγ1)
          ((radScale R ρ j)⁻¹ • x) := by
      simpa only [phaseFiniteContourPatchVorticity, circularPhasePatchVorticity,
        finiteCircularInterfaceStrength, finiteCircularInitialContours, if_neg hj,
        Submodule.coe_smul, circularReferenceC1] using
        phaseFiniteContourPatchVorticity_scale circularContourStrengths
          (fun i => circularReferenceC1 hγ hγ1 i) (ampScale A₀ b j) (hr j).ne' x
    rw [he, circularPhasePatchVorticity_reference hγ hγ1]
    simp only [datumTerm, map_smul]

theorem transported_finitePeriodicLabel_eq_phaseContours {s A₀ b R ρ : ℝ}
    (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N : ℕ) (j : Fin (N + 1))
    {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
        (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Z (j, i))))
    {x : R2} (hx : x ∈ torusBox) :
    S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t x =
      phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        (fun i => Z (j, i)) (centeredComplexHomeomorph.symm x) := by
  apply S.transportedScalar_finitePhase_eq_of_domain_images
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)
    (fun i => Z (j, i)) _ ?_ t ht hstartbox hendbox himages hx
  intro y hy
  change periodicCenteredSource (P.finitePlanarLabel s A₀ b R ρ N j) y = _
  rw [periodicCenteredSource_eq_on_box
    (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) hy]
  have hh := P.finiteCircularInitial_label_density_eq (s := s) (A₀ := A₀) (b := b)
    hR hρ N j (centeredComplexHomeomorph.symm y)
  simpa only [centeredComplexHomeomorph_symm_apply, LinearIsometryEquiv.apply_symm_apply] using hh.symm

end CircularMaterialTransferProfile
end Euler2D

end
