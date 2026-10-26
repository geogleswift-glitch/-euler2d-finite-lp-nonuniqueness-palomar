module

public import RequestProject.Euler.CircularFinitePhaseLabelIdentification
public import RequestProject.Euler.NormalizedFiniteLabelTransport

/-! A single integrable planar label of the original finite datum is
transported by the same actual particles. Its normalization at time zero
is the original unscaled patch. Domain images identify its planar density
globally, without periodizing the source in a planar L1 argument. -/

@[expose] public section

set_option maxHeartbeats 7000000
set_option maxRecDepth 5000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem singlePlanarSource_eq_phase_of_domain_images
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Zstart Zend : ι → ContourC1Space γ) (q₀ : R2 → ℝ)
    (hinit : ∀ y, q₀ y = phaseFiniteContourPatchVorticity g Zstart (centeredComplexHomeomorph.symm y))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zstart i))) =
      complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) (x : R2) :
    q₀ (S.backward t x) = phaseFiniteContourPatchVorticity g Zend (centeredComplexHomeomorph.symm x) := by
  classical
  rw [hinit, phaseFiniteContourPatchVorticity_eq_physical_indicators,
    phaseFiniteContourPatchVorticity_eq_physical_indicators]
  apply Finset.sum_congr rfl
  intro i _
  have hm : S.backward t x ∈ complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zstart i)) ↔
      x ∈ complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i)) := by
    rw [← himages i]
    constructor
    · intro hx
      exact ⟨S.backward t x, hx, S.forward_backward t ht x⟩
    · rintro ⟨y, hy, hyx⟩
      rw [← hyx, S.backward_forward t ht y]
      exact hy
  by_cases hx : x ∈ complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))
  · rw [indicator_of_mem (hm.mpr hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (fun h => hx (hm.mp h)), indicator_of_notMem hx]

end BoundedEulerParticleSystem

namespace CircularMaterialTransferProfile

variable {γ : ℝ≥0} {hγ : 0 < γ} {hγ1 : (γ : ℝ) < 1}
    (P : CircularMaterialTransferProfile hγ hγ1)

def finiteSinglePlanarInitialLabel (s A₀ b R ρ : ℝ) (N j : ℕ) (x : R2) : ℝ :=
  P.finitePlanarLabel s A₀ b R ρ N j (x - torusCenter)

theorem normalized_finiteSinglePlanarInitialLabel_zero
    {s A₀ b R ρ : ℝ} (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (N j : ℕ) {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T) (hT : 0 ≤ T) (z : R2) :
    S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) 0 z =
        if j = N then circularPhasePatchPlanarVorticity (P.ancient s) z else cellW z := by
  have hback (x : R2) : S.backward 0 x = x := by
    simpa only [S.initial] using S.backward_forward 0 ⟨le_rfl, hT⟩ x
  have hAN : 0 < ampScale A₀ b j := by unfold ampScale; positivity
  have hr : 0 < radScale R ρ j := radScale_pos hR hρ j
  by_cases hj : j = N
  · subst j
    simp only [BoundedEulerParticleSystem.normalizedPlanarLabelSource, hback,
      finiteSinglePlanarInitialLabel, add_sub_cancel_right, finitePlanarLabel,
      if_pos rfl, ite_true, finiteBaseDensity, inv_smul_smul₀ hr.ne', ← mul_assoc,
      inv_mul_cancel₀ hAN.ne', one_mul]
  · simp only [BoundedEulerParticleSystem.normalizedPlanarLabelSource, hback,
      finiteSinglePlanarInitialLabel, add_sub_cancel_right, finitePlanarLabel,
      if_neg hj, datumTerm, inv_smul_smul₀ hr.ne', ← mul_assoc,
      inv_mul_cancel₀ hAN.ne', one_mul]

theorem integrable_normalized_finiteSinglePlanarLabel
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hA : 0 < A₀) (hb : 0 < b) (hR : 0 < R) (hρ : 0 < ρ)
    (N j : ℕ) {f : Lp ℝ 2 μT} {T t : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (harea : MeasurePreserving (S.forward t) volume volume) :
    Integrable (S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hback : S.backward 0 = id := by
    funext x
    simpa only [S.initial, id_eq] using S.backward_forward 0 ⟨le_rfl, hT⟩ x
  apply S.integrable_normalizedPlanarLabelSource _ _ (radScale_pos hR hρ j) ⟨le_rfl, hT⟩ ht
    (by rw [hback]; exact MeasurePreserving.id volume) harea
  have he : S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j)
      (ampScale A₀ b j) (radScale R ρ j) 0 =
        if j = N then circularPhasePatchPlanarVorticity (P.ancient s) else cellW := by
    funext z
    rw [P.normalized_finiteSinglePlanarInitialLabel_zero hA hb hR hρ N j S hT z]
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · exact integrable_circularPhasePatchPlanarVorticity hγ hγ1 (P.ancient_domain s hs)
  · exact memLp_one_iff_integrable.mp (cellW_memLp 1)

theorem normalized_finiteSinglePlanarLabel_eq_phaseContours
    {s A₀ b R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (N : ℕ) (j : Fin (N + 1))
    {f : Lp ℝ 2 μT} {T t : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (Zend : Fin 2 → ContourC1Space γ)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) (A r : ℝ) (z : R2) :
    S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j) A r t z =
      A⁻¹ * phaseFiniteContourPatchVorticity (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
        Zend (centeredComplexHomeomorph.symm (r • z + torusCenter)) := by
  unfold BoundedEulerParticleSystem.normalizedPlanarLabelSource
  congr 1
  apply S.singlePlanarSource_eq_phase_of_domain_images
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)
    Zend _ ?_ ht himages
  intro y
  have hh := P.finiteCircularInitial_label_density_eq (s := s) (A₀ := A₀) (b := b)
    hR hρ N j (centeredComplexHomeomorph.symm y)
  simpa only [finiteSinglePlanarInitialLabel, centeredComplexHomeomorph_symm_apply,
    LinearIsometryEquiv.apply_symm_apply] using hh.symm

theorem normalized_finiteSinglePlanarLabel_eq_periodicLabel_on_chart
    {s A₀ b R ρ : ℝ} (hs : s ≤ 0) (hR : 0 < R) (hRmax : R ≤ 1 / 2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (N : ℕ) (j : Fin (N + 1))
    {f : Lp ℝ 2 μT} {T t : ℝ} (S : BoundedEulerParticleSystem f T)
    (ht : t ∈ Icc (0 : ℝ) T) (Zend : Fin 2 → ContourC1Space γ)
    (hstartbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val) ⊆ torusBox)
    (hendbox : ∀ i, complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i)) ⊆ torusBox)
    (himages : ∀ i, S.forward t '' (complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ
      (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)) =
        complexTorusPoint '' contourRadialFill (ContourC1Space.lift γ (Zend i))) (A r : ℝ)
    {z : R2} (hz : r • z + torusCenter ∈ torusBox) :
    S.normalizedPlanarLabelSource (P.finiteSinglePlanarInitialLabel s A₀ b R ρ N j) A r t z =
      A⁻¹ * S.transportedScalar (P.finitePeriodicLabel s A₀ b R ρ N j) t (r • z + torusCenter) := by
  have hperiodic := S.transportedScalar_finitePhase_eq_of_domain_images
    (fun i => finiteCircularInterfaceStrength A₀ b (j, i))
    (fun i => (finiteCircularInitialContours hγ hγ1 R ρ (P.ancient s) N (j, i)).val)
    Zend (P.finitePeriodicLabel s A₀ b R ρ N j) (by
      intro y hy
      change periodicCenteredSource (P.finitePlanarLabel s A₀ b R ρ N j) y = _
      rw [periodicCenteredSource_eq_on_box
        (P.finitePlanarLabel_zero_of_one_le_norm hs hR hRmax hρ hρ1 N j) hy]
      have hh := P.finiteCircularInitial_label_density_eq (s := s) (A₀ := A₀) (b := b)
        hR hρ N j (centeredComplexHomeomorph.symm y)
      simpa only [centeredComplexHomeomorph_symm_apply, LinearIsometryEquiv.apply_symm_apply] using hh.symm)
    t ht hstartbox hendbox himages hz
  exact (P.normalized_finiteSinglePlanarLabel_eq_phaseContours hR hρ N j S ht Zend himages A r z).trans
    (congrArg (fun u : ℝ => A⁻¹ * u) hperiodic.symm)

end CircularMaterialTransferProfile
end Euler2D

end
