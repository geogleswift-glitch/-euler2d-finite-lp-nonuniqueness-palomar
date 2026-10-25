module

public import RequestProject.Euler.CircularFinitePlanarVelocityDecomposition
public import RequestProject.Euler.CircularFiniteAncestorRigidVelocity
public import RequestProject.Euler.CircularPhysicalSelfVelocity

/-! The full physical source of the same finite Euler system splits
at its active cell into the original self field, the explicit ancestor
rigid rotation, the true ancestor residuals, and the actual inner
cluster. No contour description of the deeper labels is required. -/

@[expose] public section

set_option maxHeartbeats 6000000
set_option maxRecDepth 4000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D
namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem velocityC_physicalFiniteDensity_eq_active_rigid_residual_cluster
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T) (t : ℝ) {x : ℂ}
    (hx : ∀ j : Fin k, ‖x‖ ≤ cellA * radScale R ρ j) :
    let liftj : Fin k → Fin (N + 1) := fun j => ⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩
    velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x =
      velocityC (boxedComplexDensity
        (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N k) t)) x +
      (finiteAncestorAngularVelocity A₀ b k : ℂ) * I * x +
      (∑ j : Fin k, velocityC
        (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (liftj j) S t) x) +
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  dsimp only
  rw [P.velocityC_physicalFiniteDensity_eq_outer_add_cluster hs hA hb hR hRmax hρ hρ1
    N k hk S t x, Finset.sum_range_succ]
  have hanc := P.velocityC_finiteAncestors_eq_rigid_add_residuals
    hs hA hb hR hRmax hρ hρ1 N k hk S t hx
  dsimp only at hanc
  have hsum := Fin.sum_univ_eq_sum_range (fun j : ℕ => velocityC (boxedComplexDensity
    (S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t)) x) k
  rw [hsum] at hanc
  rw [hanc]
  abel

theorem velocityC_physicalFiniteDensity_eq_activeSelf_rigid_residual_cluster
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 ≤ A₀) (hb : 0 < b)
    (hR : 0 < R) (hRmax : R ≤ 1 / 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N k : ℕ) (hk : k ≤ N) {f : Lp ℝ 2 μT} {T : ℝ}
    (S : BoundedEulerParticleSystem f T)
    (Z : FiniteCircularIndex N → ContourC1Space γ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (W : Fin 2 → LittleContourSpace γ) (hW : W ∈ circularQuarterPhaseDomain hγ hγ1)
    (hscale : ∀ i, Z (⟨k, Nat.lt_succ_of_le hk⟩, i) = radScale R ρ k • (W i).val)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨k, Nat.lt_succ_of_le hk⟩, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill
      (ContourC1Space.lift γ (Z (⟨k, Nat.lt_succ_of_le hk⟩, i))) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill
      (ContourC1Space.lift γ (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N
        (⟨k, Nat.lt_succ_of_le hk⟩, i)).val)) =
      complexTorusPoint '' contourRadialFill
        (ContourC1Space.lift γ (Z (⟨k, Nat.lt_succ_of_le hk⟩, i))))
    (i : Fin 2) (θ : ℝ)
    (hx : ∀ j : Fin k, ‖radScale R ρ k • LittleContourSpace.lift γ (W i) θ‖ ≤
      cellA * radScale R ρ j) :
    let x := radScale R ρ k • LittleContourSpace.lift γ (W i) θ
    let liftj : Fin k → Fin (N + 1) := fun j => ⟨j, j.isLt.trans_le (Nat.le_succ_of_le hk)⟩
    velocityC (S.physicalComplexSource (P.finiteInitialPeriodicDensity s A₀ b R ρ N) t) x =
      (ampScale A₀ b k * radScale R ρ k) •
        LittleContourSpace.lift γ (circularBanachField hγ hγ1 W i) θ +
      (finiteAncestorAngularVelocity A₀ b k : ℂ) * I * x +
      (∑ j : Fin k, velocityC
        (P.finiteOuterLabelComplexPerturbation s A₀ b R ρ N (liftj j) S t) x) +
      velocityC (P.finiteInnerClusterComplexSource s A₀ b R ρ N k S t) x := by
  dsimp only
  rw [P.velocityC_physicalFiniteDensity_eq_active_rigid_residual_cluster
    hs hA hb hR hRmax hρ hρ1 N k hk S t hx]
  congr 3
  have hlabel := funext (P.boxed_transported_finitePeriodicLabel_eq_phaseContours
    (A₀ := A₀) (b := b) hs hR hRmax hρ hρ1 N
    (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1)) S Z t ht hstartbox hendbox himages)
  change velocityC (boxedComplexDensity (S.transportedScalar
    (P.finitePeriodicLabel s A₀ b R ρ N (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (N + 1))) t)) _ = _
  rw [hlabel]
  simp only [hscale, finiteCircularInterfaceStrength, Fin.val_mk]
  exact circularPhysicalSelfVelocity_eq_scaled_field hγ hγ1 hW _ (radScale_pos hR hρ k) i θ

end CircularMaterialTransferProfile
end Euler2D

end
