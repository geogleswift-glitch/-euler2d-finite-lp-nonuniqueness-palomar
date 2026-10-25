module

public import RequestProject.Euler.CircularAncientFiniteInitialFamily

/-! The actual finite contour initial data has exactly the vorticity used
to construct the genuine finite torus Euler systems. Both the circular
outer layers and the same scaled ancient inner material cell are retained. -/

@[expose] public section

set_option maxHeartbeats 3000000

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal

namespace Euler2D

theorem mem_contourRadialFill_smul_iff {r : ℝ} (hr : r ≠ 0)
    (z : ℝ → ℂ) (x : ℂ) :
    x ∈ contourRadialFill (fun θ => r • z θ) ↔ r⁻¹ • x ∈ contourRadialFill z := by
  constructor
  · rintro ⟨θ, t, ht0, ht1, hx⟩
    refine ⟨θ, t, ht0, ht1, ?_⟩
    rw [hx]
    simp only [smul_smul]
    congr 1
    field_simp
  · rintro ⟨θ, t, ht0, ht1, hx⟩
    refine ⟨θ, t, ht0, ht1, ?_⟩
    calc
      x = r • (r⁻¹ • x) := by simp only [smul_smul, mul_inv_cancel₀ hr, one_smul]
      _ = r • (t • z θ) := congrArg (fun u : ℂ => r • u) hx
      _ = t • (r • z θ) := smul_comm r t _

theorem phaseContourPatchVorticity_smul {γ : ℝ≥0} {r : ℝ} (hr : r ≠ 0)
    (Z : ContourC1Space γ) (x : ℂ) :
    phaseContourPatchVorticity (r • Z) x = phaseContourPatchVorticity Z (r⁻¹ • x) := by
  have hm := mem_contourRadialFill_smul_iff hr (ContourC1Space.lift γ Z) x
  change (contourRadialFill (fun θ => r • ContourC1Space.lift γ Z θ)).indicator
      (fun _ => (1 : ℝ)) x =
    (contourRadialFill (ContourC1Space.lift γ Z)).indicator (fun _ => (1 : ℝ)) (r⁻¹ • x)
  by_cases hx : r⁻¹ • x ∈ contourRadialFill (ContourC1Space.lift γ Z)
  · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (fun h => hx (hm.mp h)), indicator_of_notMem hx]

theorem phaseFiniteContourPatchVorticity_scale {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ι → ContourC1Space γ) (A : ℝ) {r : ℝ} (hr : r ≠ 0) (x : ℂ) :
    phaseFiniteContourPatchVorticity (fun i => A * g i) (fun i => r • Z i) x =
      A * phaseFiniteContourPatchVorticity g Z (r⁻¹ • x) := by
  simp only [phaseFiniteContourPatchVorticity, phaseContourPatchVorticity_smul hr,
    Finset.mul_sum, mul_assoc]

theorem contourRadialFill_refCircle {r : ℝ} (hr : 0 < r) :
    contourRadialFill (refCircle r) = ball (0 : ℂ) r := by
  change contourRadialFill (fun θ => (r : ℂ) * exp ((θ : ℂ) * I)) = _
  rw [← starDomain_eq_contourRadialFill continuous_const (fun _ => rfl) hr (fun _ => le_rfl)]
  ext x
  simp only [starDomain, mem_setOf_eq, mem_ball_zero_iff]

theorem phaseContourPatchVorticity_circularReference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (i : Fin 2) (x : ℂ) :
    phaseContourPatchVorticity (circularReferenceC1 hγ hγ1 i) x =
      (ball (0 : ℂ) (circularContourRadii i)).indicator (fun _ => (1 : ℝ)) x := by
  unfold phaseContourPatchVorticity
  rw [lift_circularReferenceC1, contourRadialFill_refCircle (circularContourRadii_bounds i).1]

theorem circularPhasePatchVorticity_reference {γ : ℝ≥0}
    (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1) (x : ℂ) :
    circularPhasePatchVorticity (littleCircularReference hγ hγ1) x = cellW (complexPhysicalPlane x) := by
  change (∑ i : Fin 2, circularContourStrengths i *
    phaseContourPatchVorticity (circularReferenceC1 hγ hγ1 i) x) = _
  simp only [phaseContourPatchVorticity_circularReference, Fin.sum_univ_two,
    circularContourStrengths, circularContourRadii, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  have hnorm : ‖torusVec x.re x.im‖ = ‖x‖ := complexPhysicalPlane.norm_map x
  by_cases ha : ‖x‖ < cellA <;> by_cases h1 : ‖x‖ < 1 <;>
    simp [cellW, twoInterface, mem_ball, dist_zero_right, hnorm, ha, h1] <;> ring

def finiteCircularInterfaceStrength (A₀ b : ℝ) {N : ℕ} (p : FiniteCircularIndex N) : ℝ :=
  ampScale A₀ b p.1 * circularContourStrengths p.2

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem finiteCircularInitial_density_eq {s A₀ b R ρ : ℝ}
    (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) (x : ℂ) :
    phaseFiniteContourPatchVorticity (finiteCircularInterfaceStrength A₀ b)
      (fun p => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val) x =
        P.finiteInitialPlanarDensity s A₀ b R ρ N (complexPhysicalPlane x) := by
  have hr (j : ℕ) : 0 < radScale R ρ j := mul_pos hR (pow_pos hρ j)
  have hblock (j : Fin (N + 1)) :
      (∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
        phaseContourPatchVorticity
          (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val x) =
      if (j : ℕ) = N then P.finiteBaseDensity s A₀ b R ρ N (complexPhysicalPlane x)
        else datumTerm A₀ b R ρ j (complexPhysicalPlane x) := by
    by_cases hj : (j : ℕ) = N
    · rw [if_pos hj]
      have he : (∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
          phaseContourPatchVorticity
            (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val x) =
          ampScale A₀ b N * circularPhasePatchVorticity (P.ancient s) ((radScale R ρ N)⁻¹ • x) := by
        simpa only [phaseFiniteContourPatchVorticity, circularPhasePatchVorticity,
          finiteCircularInterfaceStrength, finiteCircularInitialContours, hj, if_pos rfl] using
          phaseFiniteContourPatchVorticity_scale circularContourStrengths
            (fun i => (P.ancient s i).val) (ampScale A₀ b N) (hr N).ne' x
      rw [he]
      simp only [finiteBaseDensity, circularPhasePatchPlanarVorticity, map_smul,
        LinearIsometryEquiv.symm_apply_apply]
    · rw [if_neg hj]
      have he : (∑ i : Fin 2, finiteCircularInterfaceStrength A₀ b (j, i) *
          phaseContourPatchVorticity
            (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val x) =
          ampScale A₀ b j * circularPhasePatchVorticity (littleCircularReference hγ hγ1)
            ((radScale R ρ j)⁻¹ • x) := by
        simpa only [phaseFiniteContourPatchVorticity, circularPhasePatchVorticity,
          finiteCircularInterfaceStrength, finiteCircularInitialContours, if_neg hj] using
          phaseFiniteContourPatchVorticity_scale circularContourStrengths
            (fun i => circularReferenceC1 hγ hγ1 i) (ampScale A₀ b j) (hr j).ne' x
      rw [he, circularPhasePatchVorticity_reference hγ hγ1]
      simp only [datumTerm, map_smul]
  change (∑ p : FiniteCircularIndex N, finiteCircularInterfaceStrength A₀ b p *
    phaseContourPatchVorticity (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N p).val x) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hblock]
  rw [Fin.sum_univ_castSucc]
  have hprefix : (∑ j : Fin N,
      if (j.castSucc : ℕ) = N then P.finiteBaseDensity s A₀ b R ρ N (complexPhysicalPlane x)
        else datumTerm A₀ b R ρ j.castSucc (complexPhysicalPlane x)) =
      ∑ j : Fin N, datumTerm A₀ b R ρ j (complexPhysicalPlane x) := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_castSucc, if_neg (Nat.ne_of_lt j.isLt)]
  rw [hprefix]
  rw [if_pos (show (Fin.last N : ℕ) = N from rfl)]
  change (∑ j : Fin N, datumTerm A₀ b R ρ j (complexPhysicalPlane x)) +
      P.finiteBaseDensity s A₀ b R ρ N (complexPhysicalPlane x) = _
  have hsum : (∑ j : Fin N, datumTerm A₀ b R ρ j (complexPhysicalPlane x)) =
      ∑ j ∈ Finset.range N, datumTerm A₀ b R ρ j (complexPhysicalPlane x) :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ => datumTerm A₀ b R ρ j (complexPhysicalPlane x)) N
  rw [hsum]
  rfl

end CircularMaterialTransferProfile

end Euler2D

end
