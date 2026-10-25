module

public import RequestProject.Euler.FinitePhaseActualCorrectionTransport
public import RequestProject.Euler.TorusPhysicalLabelComplexField

/-! Genuine material transport for a finite set of active interfaces,
with the same bounded logarithmic field left outside the contour sum. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem exists_finitePhase_commonField_velocity
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (E : ℝ → ℂ → ℂ) (ME CE : ℝ≥0)
    (hEc : Continuous (Function.uncurry E))
    (hEM : ∀ t z, ‖E t z‖ ≤ ME)
    (hElog : ∀ t z w, ‖z - w‖ ≤ 1 / 2 →
      ‖E t z - E t w‖ ≤ CE * logFlowModulus ‖z - w‖)
    (hEdiv : ∀ t, IsPlanarWeaklyDivergenceFree (fun x : R2 =>
      complexPhysicalPlane (E t (complexPhysicalPlane.symm x))))
    {D : ℝ} (hD : 0 ≤ D)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z t i) - Z₀ i‖ < r i / 4) :
    ∃ M C : ℝ≥0, ∃ v : ℝ → ℂ → ℂ,
      Continuous (Function.uncurry v) ∧
      (∀ t ∈ Icc (0 : ℝ) D, ∀ z,
        v t z = velocityC (phaseFiniteContourPatchVorticity g (Z t)) z + E t z) ∧
      (∀ t z, ‖v t z‖ ≤ M) ∧
      (∀ t z w, ‖z - w‖ ≤ 1 / 2 →
        ‖v t z - v t w‖ ≤ C * logFlowModulus ‖z - w‖) ∧
      ∀ t, IsPlanarWeaklyDivergenceFree (fun x : R2 =>
        complexPhysicalPlane (v t (complexPhysicalPlane.symm x))) := by
  let Zi : Icc (0 : ℝ) D → ι → ContourC1Space γ := fun t => Z t
  have hZi (i : ι) : Continuous (fun t : Icc (0 : ℝ) D => Zi t i) := (hZ i).restrict
  let τ : ℝ → Icc (0 : ℝ) D := projIcc 0 D hD
  let W : ℝ → ι → ContourC1Space γ := fun t => Zi (τ t)
  have hW (i : ι) : Continuous (fun t => W t i) :=
    (hZi i).comp (continuous_projIcc (h := hD))
  have hWp (t : ℝ) : ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (W t i) - Z₀ i‖ < r i / 4 :=
    hphase (τ t) (τ t).property
  let ω : ℝ → ℂ → ℝ := fun t => phaseFiniteContourPatchVorticity g (W t)
  have hωi (t : ℝ) : Integrable (ω t) := by
    obtain ⟨b, hb⟩ := hWp t
    exact integrable_phaseFiniteContourPatchVorticity g (W t) Z₀ r hr href b (fun i => (hb i).le)
  have hωB (t : ℝ) (z : ℂ) : |ω t z| ≤ finiteContourPatchSupBound g := by
    obtain ⟨b, hb⟩ := hWp t
    exact abs_phaseFiniteContourPatchVorticity_le g (W t) Z₀ r hr href b (fun i => (hb i).le) z
  have hωmass (t : ℝ) : (∫ z, |ω t z|) ≤ finiteContourPatchMassBound g r := by
    obtain ⟨b, hb⟩ := hWp t
    exact integral_abs_phaseFiniteContourPatchVorticity_le g (W t) Z₀ r hr href b (fun i => (hb i).le)
  let vp : ℝ → ℂ → ℂ := fun t => velocityC (ω t)
  have hvp : Continuous (Function.uncurry vp) :=
    continuous_phaseFiniteContourPatchVelocity g hW Z₀ r hr href hWp
  let B := finiteContourPatchSupBound g + finiteContourPatchMassBound g r
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  let MB : ℝ≥0 := NNReal.mk (B + ME) (add_nonneg hB ME.2)
  let CB : ℝ≥0 := NNReal.mk (8 * B + CE) (by positivity)
  let v : ℝ → ℂ → ℂ := fun t z => vp t z + E t z
  have hv : Continuous (Function.uncurry v) := hvp.add hEc
  have hvM (t : ℝ) (z : ℂ) : ‖v t z‖ ≤ MB := by
    have hp := velocity_bound_split (hωi t) (hωB t) z (d := 1) (by norm_num)
    have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hi : 0 ≤ ∫ y, |ω t y| := integral_nonneg (fun _ => abs_nonneg _)
    have hpB : ‖vp t z‖ ≤ B := by
      simp only [mul_one] at hp
      exact hp.trans (add_le_add le_rfl ((div_le_self hi hπ).trans (hωmass t)))
    exact (norm_add_le _ _).trans (add_le_add hpB (hEM t z))
  have hvlog (t : ℝ) (z w : ℂ) (hzw : ‖z - w‖ ≤ 1 / 2) :
      ‖v t z - v t w‖ ≤ CB * logFlowModulus ‖z - w‖ := by
    have hp := velocityC_logFlowModulus_le (hωi t) (hωB t) (hωmass t) hzw
    have he : v t z - v t w = (vp t z - vp t w) + (E t z - E t w) := by
      dsimp only [v]
      abel
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add hp (hElog t z w hzw)).trans_eq (by
      change 8 * B * logFlowModulus ‖z - w‖ + (CE : ℝ) * logFlowModulus ‖z - w‖ =
        (8 * B + (CE : ℝ)) * logFlowModulus ‖z - w‖
      ring))
  have hvdiv (t : ℝ) : IsPlanarWeaklyDivergenceFree (fun x : R2 =>
      complexPhysicalPlane (v t (complexPhysicalPlane.symm x))) := by
    have hpct : Continuous (fun x : R2 =>
        complexPhysicalPlane (vp t (complexPhysicalPlane.symm x))) :=
      complexPhysicalPlane.continuous.comp (Continuous.comp
        (f := fun x : R2 => (t, complexPhysicalPlane.symm x))
        (g := fun p : ℝ × ℂ => vp p.1 p.2) hvp
        (continuous_const.prodMk complexPhysicalPlane.symm.continuous))
    have hEct : Continuous (fun x : R2 =>
        complexPhysicalPlane (E t (complexPhysicalPlane.symm x))) :=
      complexPhysicalPlane.continuous.comp (Continuous.comp
        (f := fun x : R2 => (t, complexPhysicalPlane.symm x))
        (g := fun p : ℝ × ℂ => E p.1 p.2) hEc
        (continuous_const.prodMk complexPhysicalPlane.symm.continuous))
    have he : (fun x : R2 => complexPhysicalPlane (v t (complexPhysicalPlane.symm x))) =
        (fun x : R2 => complexPhysicalPlane (vp t (complexPhysicalPlane.symm x)) +
          complexPhysicalPlane (E t (complexPhysicalPlane.symm x))) := by
      funext x
      exact map_add _ _ _
    rw [he]
    exact (isPlanarWeaklyDivergenceFree_velocityC (hωi t)
      (fun z => by simpa only [Real.norm_eq_abs] using hωB t z)).add
        (hEdiv t) hpct hEct
  refine ⟨MB, CB, v, hv, ?_, hvM, hvlog, hvdiv⟩
  intro t ht z
  have hWt : W t = Z t := by
    dsimp only [W, Zi, τ]
    rw [projIcc_of_mem hD ht]
  simp only [v, vp, ω, hWt]

theorem exists_finitePhase_commonField_material_area_transport
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    (E : ℝ → ℂ → ℂ) (ME CE : ℝ≥0)
    (hEc : Continuous (Function.uncurry E))
    (hEM : ∀ t z, ‖E t z‖ ≤ ME)
    (hElog : ∀ t z w, ‖z - w‖ ≤ 1 / 2 →
      ‖E t z - E t w‖ ≤ CE * logFlowModulus ‖z - w‖)
    (hEdiv : ∀ t, IsPlanarWeaklyDivergenceFree (fun x : R2 =>
      complexPhysicalPlane (E t (complexPhysicalPlane.symm x))))
    {D : ℝ} (hD : 0 ≤ D)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z t i) - Z₀ i‖ < r i / 4)
    (hmat : ∀ t ∈ Icc (0 : ℝ) D, ∀ i θ,
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (contourC1BoundaryField g (Z t) i θ + E t (ContourC1Space.lift γ (Z t i) θ)) t) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) D, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (phaseFiniteContourPatchVorticity g (Z t)) (F t a) + E t (F t a)) t) ∧
      (∀ t ∈ Icc (0 : ℝ) D, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      ∀ t ∈ Icc (0 : ℝ) D,
        (∀ i θ, F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ) ∧
        (∀ i, F t '' contourRadialFill (ContourC1Space.lift γ (Z 0 i)) =
          contourRadialFill (ContourC1Space.lift γ (Z t i))) ∧
        ∀ x, phaseFiniteContourPatchVorticity g (Z t) x =
          phaseFiniteContourPatchVorticity g (Z 0) ((F t).symm x) := by
  obtain ⟨M, C, v, hv, heq, hM, hlog, hdiv⟩ :=
    exists_finitePhase_commonField_velocity g Z Z₀ r hr href E ME CE
      hEc hEM hElog hEdiv hD hZ hphase
  obtain ⟨F, hFc, hFic, hF0, hFd, hFa⟩ :=
    exists_complex_measurePreserving_logHomeomorphFlow hv hM hlog hdiv hD
  have hZd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) (θ : ℝ) :
      HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
        (v t (ContourC1Space.lift γ (Z t i) θ)) t := by
    obtain ⟨b, hb⟩ := hphase t ht
    have hd := hmat t ht i θ
    change HasDerivAt (fun s => ContourC1Space.lift γ (Z s i) θ)
      (contourBoundaryField g (fun j => ContourC1Space.lift γ (Z t j)) i θ + _) t at hd
    rw [contourBoundaryField_eq_phase_actual_velocity g (Z t) Z₀ r hr href b (fun j => (hb j).le),
      ← heq t ht (ContourC1Space.lift γ (Z t i) θ)] at hd
    exact hd
  have hboundary (t : ℝ) (ht : t ∈ Icc (0 : ℝ) D) (i : ι) (θ : ℝ) :
      F t (ContourC1Space.lift γ (Z 0 i) θ) = ContourC1Space.lift γ (Z t i) θ :=
    logFlow_uniqueOn C.2
      (fun s hs => (hFd s hs _).continuousAt.continuousWithinAt)
      (fun s hs => (hZd s hs i θ).continuousAt.continuousWithinAt)
      (fun s hs => hFd s hs _) (fun s hs => hZd s hs i θ) (hF0 _)
      (fun s _ z w hzw => hlog s z w hzw) t ht
  have hp : ∀ s ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z s i) - Z₀ i‖ ≤ r i / 4 := by
    intro s hs
    obtain ⟨b, hb⟩ := hphase s hs
    exact ⟨b, fun i => (hb i).le⟩
  have hFinv : ContinuousOn (fun s => (F s).symm 0) (Icc (0 : ℝ) D) :=
    (hFic.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hFzero : (F 0).symm 0 = 0 := by
    rw [← hF0 ((F 0).symm 0), (F 0).apply_symm_apply]
  refine ⟨F, hFc, hFic, hF0, ?_, hFa, ?_⟩
  · intro t ht a
    simpa only [heq t ht] using hFd t ht a
  · intro t ht
    refine ⟨hboundary t ht, ?_, ?_⟩
    · intro i
      exact image_contourRadialFill_of_phase_boundary_isotopy (fun s => Z s i) (Z₀ i)
        (hr i) hD (href i)
        (fun s hs => by obtain ⟨b, hb⟩ := hp s hs; exact ⟨b i, hb i⟩)
        F hFinv hFzero (fun s hs θ => hboundary s hs i θ) ht
    · intro x
      exact phaseFiniteContourPatchVorticity_eq_initial_comp_inverse g Z Z₀ r hr hD href hp
        F hFinv hFzero hboundary ht x

end Euler2D

end
