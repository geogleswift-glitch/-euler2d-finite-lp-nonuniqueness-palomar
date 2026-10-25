module

public import RequestProject.Euler.CircularSinglePlanarLabelTransport
public import RequestProject.Euler.CircularFiniteInnerParticleConfinement
public import RequestProject.Euler.CircularFiniteRealRadialFeedback

/-! The newly rough inner cluster has a genuine radius reset on the
same Euler flow. Its current label is confined by its actual material
images; its deeper labels use the already proved particle fence. -/

@[expose] public section

set_option maxHeartbeats 10000000
set_option maxRecDepth 6500

noncomputable section

open Complex Set MeasureTheory Metric
open scoped NNReal ENNReal

namespace Euler2D

attribute [local irreducible] contourC1GraphSubmodule holderGraphSubmodule

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

theorem actual_material_label_particle_radius
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {N k : ℕ}
    {f : Lp ℝ 2 μT} {T t c δ : ℝ} {S : BoundedEulerParticleSystem f T}
    (ht : t ∈ Icc (0 : ℝ) T) (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (j : Fin (N + 1)) (hj : (j : ℕ) ≤ k) {y : R2} (hy : y ∈ torusBox)
    (hne : P.finitePeriodicLabel s A₀ b R ρ N j y ≠ 0) :
    ‖S.forward t y - torusCenter‖ ≤ (5 / 4) * radScale R ρ j := by
  have hper : P.finitePeriodicLabel s A₀ b R ρ N j y =
      P.finitePlanarLabel s A₀ b R ρ N j (y - torusCenter) :=
    periodicCenteredSource_eq_on_box
      (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) hy
  have hsingle : P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j y ≠ 0 := by
    change P.finitePlanarLabel s A₀ b R ρ N j (y - torusCenter) ≠ 0
    rw [← hper]
    exact hne
  have hinit (x : R2) :
      P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j x =
        phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
          (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)
          (centeredComplexHomeomorph.symm x) := by
    have hh := P.finiteCircularInitial_label_density_eq (s := s) (A₀ := A₀) (b := b)
      hR hρ N j (centeredComplexHomeomorph.symm x)
    simpa only [finiteSinglePlanarInitialLabel, centeredComplexHomeomorph_symm_apply,
      LinearIsometryEquiv.apply_symm_apply] using hh.symm
  have hsource := S.singlePlanarSource_eq_phase_of_domain_images
    (fun i : Fin 2 => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)
    (fun i => G.contours (j, i)) (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
    hinit ht (G.images j hj) (S.forward t y)
  rw [S.backward_forward t ht y] at hsource
  have hphase : phaseFiniteContourPatchVorticity
      (fun i => finiteCircularInterfaceStrength A₀ b (j, i)) (fun i => G.contours (j, i))
      (centeredComplexHomeomorph.symm (S.forward t y)) ≠ 0 :=
    fun hz => hsingle (hsource.trans hz)
  have hn := norm_le_of_phaseFiniteContourPatchVorticity_ne_zero
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => G.contours (j, i)) (fun i => G.reference (j, i))
    (fun i => circularContourRadii i * radScale R ρ j)
    (fun i => mul_pos (circularContourRadii_bounds i).1 (radScale_pos hR hρ j))
    (G.reference_lift j hj) (fun i => G.shifts (j, i)) (G.quarter_tube j hj)
    (R := (5 / 4) * radScale R ρ j)
    (by
      intro i
      have hh := mul_le_mul_of_nonneg_right (circularContourRadii_bounds i).2.2
        (radScale_pos hR hρ j).le
      nlinarith only [hh]) hphase
  simpa only [centeredComplexHomeomorph_symm_apply, LinearIsometryEquiv.norm_map] using hn

theorem actual_inner_particle_radius_reset
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    {f : Lp ℝ 2 μT} {T t c δ : ℝ} {S : BoundedEulerParticleSystem f T}
    (ht : t ∈ Icc (0 : ℝ) T) (G : P.FiniteOuterMaterialTube s R ρ N k S t c δ)
    (hdeeper : ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k,
      ‖S.forward t y - torusCenter‖ ≤ 2 * radScale R ρ k) :
    ∀ y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N (k - 1),
      ‖S.forward t y - torusCenter‖ ≤ 2 * ρ * radScale R ρ (k - 1) := by
  intro y hy
  obtain ⟨hybox, j, hj, hne⟩ := hy
  have hjk : k ≤ j := by
    have hh := (Finset.mem_Ico.mp hj).1
    omega
  have hbound : ‖S.forward t y - torusCenter‖ ≤ 2 * radScale R ρ k := by
    by_cases he : j = k
    · subst j
      have hn := P.actual_material_label_particle_radius hs hR hRmax hρ hρ1 ht G
        (⟨k, Nat.lt_succ_of_le hkN⟩ : Fin (N + 1)) le_rfl hybox hne
      have hr := (radScale_pos hR hρ k).le
      exact hn.trans (by nlinarith only [hr])
    · have hinner : y ∈ P.finiteInnerActiveInitialLabels s A₀ b R ρ N k :=
        ⟨hybox, j, Finset.mem_Ico.mpr ⟨by omega, (Finset.mem_Ico.mp hj).2⟩, hne⟩
      exact hdeeper y hinner
  have hstep : k = (k - 1) + 1 := by omega
  have hscale : radScale R ρ k = ρ * radScale R ρ (k - 1) := by
    conv_lhs => rw [hstep]
    simp only [radScale, pow_succ]
    ring
  rw [hscale] at hbound
  simpa only [mul_assoc] using hbound

end CircularMaterialTransferProfile
end Euler2D

end
