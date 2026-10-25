module

public import RequestProject.Euler.GlobalPlanarEulerUniqueness
public import RequestProject.Euler.CircularPhaseMaterialTransport
public import RequestProject.Euler.CircularPhaseGlobalContinuation

/-! The actual global Euler continuation agrees with the actual
material contour dynamics throughout every finite quarter-phase
window. Agreement follows from the proved singular nonlinear
particle uniqueness, not from a choice of continuation. -/

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Complex Set Filter Topology
open scoped NNReal

namespace Euler2D

theorem exists_circularPhase_globalEuler_material_agreement
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ1 : (γ : ℝ) < 1)
    (Z : ℝ → Fin 2 → LittleContourSpace γ) {T : ℝ} (hT : 0 ≤ T)
    (hZc : ContinuousOn Z (Icc (0 : ℝ) T))
    (hZm : ∀ t ∈ Icc (0 : ℝ) T, Z t ∈ circularQuarterPhaseDomain hγ hγ1)
    (hZd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt Z (circularBanachField hγ hγ1 (Z t)) t)
    (S : GlobalPlanarEulerParticleSystem (circularPhasePatchPlanarVorticity (Z 0))) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) T, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ a,
        S.forward t (complexPhysicalPlane a) = complexPhysicalPlane (F t a)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        S.vorticity t x = circularPhasePatchPlanarVorticity (Z t) x) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
        S.velocity t x = complexPhysicalPlane
          (velocityC (circularPhasePatchVorticity (Z t)) (complexPhysicalPlane.symm x)) := by
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea, htransport, hnorm⟩ :=
    exists_circularPhase_material_area_transport hγ hγ1 Z hT hZc hZm hZd
  let G : ℝ → R2 ≃ₜ R2 := fun t => complexPhysicalPlane.symm.toHomeomorph.trans
    ((F t).trans complexPhysicalPlane.toHomeomorph)
  let Zi : Icc (0 : ℝ) T → Fin 2 → LittleContourSpace γ := fun t => Z t
  let v : ℝ → ℂ → ℂ := circularPhaseVelocityOnInterval hT Zi
  have hvc : Continuous (Function.uncurry v) :=
    continuous_circularPhaseVelocityOnInterval hγ hγ1 hT Zi hZc.restrict (fun t => hZm t t.property)
  have hv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : ℂ) :
      v t a = velocityC (circularPhasePatchVorticity (Z t)) a := by
    simp only [v, circularPhaseVelocityOnInterval, projIcc_of_mem hT ht, Zi]
  let vr : ℝ → R2 → R2 := fun t x => complexPhysicalPlane (v t (complexPhysicalPlane.symm x))
  let j : ℝ × R2 → ℝ × ℂ := fun p => (p.1, complexPhysicalPlane.symm p.2)
  have hj : Continuous j := continuous_fst.prodMk (complexPhysicalPlane.symm.continuous.comp continuous_snd)
  have hvrc : Continuous (Function.uncurry vr) :=
    complexPhysicalPlane.continuous.comp (hvc.comp (f := j) hj)
  have hGc : Continuous (fun p : ℝ × R2 => G p.1 p.2) := by
    change Continuous (fun p : ℝ × R2 => complexPhysicalPlane (F p.1 (complexPhysicalPlane.symm p.2)))
    exact complexPhysicalPlane.continuous.comp (hFc.comp (f := j) hj)
  have hGa (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : MeasurePreserving (G t) volume volume :=
    complexPhysicalPlane.measurePreserving.comp ((hFarea t ht).1.comp complexPhysicalPlane.symm.measurePreserving)
  have hG0 (a : R2) : G 0 a = a := by
    change complexPhysicalPlane (F 0 (complexPhysicalPlane.symm a)) = a
    rw [hF0, LinearIsometryEquiv.apply_symm_apply]
  have hGd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a : R2) :
      HasDerivAt (fun s => G s a) (vr t (G t a)) t := by
    have hd := complexPhysicalPlane.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hFd t ht (complexPhysicalPlane.symm a))
    have he : vr t (G t a) = complexPhysicalPlane
        (velocityC (circularPhasePatchVorticity (Z t)) (F t (complexPhysicalPlane.symm a))) := by
      change complexPhysicalPlane (v t (complexPhysicalPlane.symm
        (complexPhysicalPlane (F t (complexPhysicalPlane.symm a))))) = _
      rw [LinearIsometryEquiv.symm_apply_apply, hv t ht]
    rw [he]
    exact hd
  have hwr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      circularPhasePatchPlanarVorticity (Z t) =
        fun x => circularPhasePatchPlanarVorticity (Z 0) ((G t).symm x) := by
    funext x
    change circularPhasePatchVorticity (Z t) (complexPhysicalPlane.symm x) =
      circularPhasePatchVorticity (Z 0) (complexPhysicalPlane.symm
        (complexPhysicalPlane ((F t).symm (complexPhysicalPlane.symm x))))
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact htransport t ht _
  have hvr (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
      vr t x = planarKernelVelocity kernelK (circularPhasePatchPlanarVorticity (Z t)) x := by
    dsimp only [vr]
    rw [hv t ht]
    exact complexPhysicalPlane_velocityC _ x
  let P : PlanarMaterialParticleFlow kernelK (circularPhasePatchPlanarVorticity (Z 0)) T := {
    velocity := vr
    forward := fun t a => G t a
    continuous_velocity := hvrc
    continuous_forward := hGc
    initial := hG0
    derivative := hGd
    source_integral := fun t ht x => by
      rw [hvr t ht x, hwr t ht]
      exact (planarMaterialBiotSavart_eq_spatial _ (G t) (hGa t ht) x).symm }
  have hw0 := integrable_circularPhasePatchPlanarVorticity hγ hγ1 (hZm 0 ⟨le_rfl, hT⟩)
  have hb0 := norm_circularPhasePatchPlanarVorticity_le hγ hγ1 (hZm 0 ⟨le_rfl, hT⟩)
  have heq := P.forward_eq_of_measurePreserving_homeomorphs (S.restrictFinite T).toSingularMaterialFlow
    hw0 hb0 hT (fun t => G t) (S.restrictFinite T).particles.homeomorph
    (fun _ => rfl) (fun _ => rfl) (fun t => hGa t t.property)
    (fun t => S.forward_area t t.property.1)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) : G t x = S.forward t x := heq t ht x
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) : S.backward t x = (G t).symm x := by
    have hh := congrArg (S.backward t) (hf t ht ((G t).symm x))
    rw [(G t).apply_symm_apply, S.left_inv t ht.1] at hh
    exact hh
  have hden (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
      S.vorticity t x = circularPhasePatchPlanarVorticity (Z t) x := by
    change circularPhasePatchPlanarVorticity (Z 0) (S.backward t x) = _
    rw [hb t ht]
    exact (congrFun (hwr t ht) x).symm
  refine ⟨F, hFc, hFic, hF0, hFarea, ?_, hden, ?_⟩
  · intro t ht a
    have hh := (hf t ht (complexPhysicalPlane a)).symm
    simpa only [G, Homeomorph.trans_apply, LinearIsometryEquiv.coe_toHomeomorph,
      LinearIsometryEquiv.symm_apply_apply] using hh
  · intro t ht x
    rw [S.selfconsistent t x]
    change planarKernelVelocity kernelK (S.vorticity t) x = _
    have hd : S.vorticity t = circularPhasePatchPlanarVorticity (Z t) := funext (hden t ht)
    rw [hd]
    exact (complexPhysicalPlane_velocityC _ x).symm

end Euler2D

end
