module

public import RequestProject.Euler.FiniteContourActualCorrectionParticleFlow
public import RequestProject.Euler.ContourPhaseVelocityContinuity
public import RequestProject.Euler.PhaseDomainTransport

/-! Actual forced area-preserving plane particles across arbitrary phase
charts. The material parametrization is never changed with time; only
the intrinsic patch domains are used to construct its velocity. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D
namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finitePhase_actualCorrection_velocity
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z t i) - Z₀ i‖ < r i / 4) :
    ∃ M C : ℝ≥0, ∃ v : ℝ → ℂ → ℂ,
      Continuous (Function.uncurry v) ∧
      (∀ t ∈ Icc (0 : ℝ) D, ∀ z, v t z = velocityC (phaseFiniteContourPatchVorticity g (Z t)) z +
        planeComplexEquiv (S.correctionLabelField t (complexTorusPoint z))) ∧
      (∀ t z, ‖v t z‖ ≤ M) ∧
      (∀ t z w, ‖z - w‖ ≤ 1 / 2 → ‖v t z - v t w‖ ≤ C * logFlowModulus ‖z - w‖) ∧
      ∀ t, IsPlanarWeaklyDivergenceFree (fun x : R2 =>
        complexPhysicalPlane (v t (complexPhysicalPlane.symm x))) := by
  let Zi : Icc (0 : ℝ) D → ι → ContourC1Space γ := fun t => Z t
  have hZi (i : ι) : Continuous (fun t : Icc (0 : ℝ) D => Zi t i) := (hZ i).restrict
  let τ : ℝ → Icc (0 : ℝ) D := projIcc 0 D hD
  let W : ℝ → ι → ContourC1Space γ := fun t => Zi (τ t)
  have hW (i : ι) : Continuous (fun t => W t i) := (hZi i).comp (continuous_projIcc (h := hD))
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
  obtain ⟨M, hM, hMc⟩ := S.exists_uniform_bound_correctionLabelField
  obtain ⟨L, hL⟩ := S.exists_lipschitzWith_correctionLabelField
  let B := finiteContourPatchSupBound g + finiteContourPatchMassBound g r
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  let MB : ℝ≥0 := ⟨B + M, add_nonneg hB hM⟩
  let CB : ℝ≥0 := ⟨8 * B + L, by positivity⟩
  let E : ℝ → ℂ → ℂ := fun t z => complexPhysicalPlane.symm
    (S.correctionLabelField t (complexTorusPoint z))
  have hct : Continuous (fun z : ℂ => complexTorusPoint z) :=
    complexPhysicalPlane.continuous.add continuous_const
  have hEc : Continuous (Function.uncurry E) :=
    complexPhysicalPlane.symm.continuous.comp (Continuous.comp
      (f := fun p : ℝ × ℂ => (p.1, complexTorusPoint p.2))
      (g := fun p : ℝ × R2 => S.correctionLabelField p.1 p.2)
      S.continuous_correctionLabelField (continuous_fst.prodMk (hct.comp continuous_snd)))
  let v : ℝ → ℂ → ℂ := fun t z => vp t z + E t z
  have hv : Continuous (Function.uncurry v) := hvp.add hEc
  have hvM (t : ℝ) (z : ℂ) : ‖v t z‖ ≤ MB := by
    have hp := velocity_bound_split (hωi t) (hωB t) z (d := 1) (by norm_num)
    have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hi : 0 ≤ ∫ y, |ω t y| := integral_nonneg (fun _ => abs_nonneg _)
    have hpB : ‖vp t z‖ ≤ B := by
      simp only [mul_one] at hp
      exact hp.trans
        (add_le_add le_rfl ((div_le_self hi hπ).trans (hωmass t)))
    have hEM : ‖E t z‖ ≤ M := by simpa only [E, LinearIsometryEquiv.norm_map] using hMc t (complexTorusPoint z)
    exact (norm_add_le _ _).trans (add_le_add hpB hEM)
  have hvlog (t : ℝ) (z w : ℂ) (hzw : ‖z - w‖ ≤ 1 / 2) :
      ‖v t z - v t w‖ ≤ CB * logFlowModulus ‖z - w‖ := by
    have hm : ‖z - w‖ ≤ logFlowModulus ‖z - w‖ := by
      have hp := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (z - w))
        (Real.log_nonpos (norm_nonneg _) (hzw.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
      dsimp only [logFlowModulus]
      linarith
    have hc := (hL t).dist_le_mul (complexTorusPoint z) (complexTorusPoint w)
    rw [dist_eq_norm, dist_eq_norm] at hc
    have he : ‖complexTorusPoint z - complexTorusPoint w‖ = ‖z - w‖ := by
      simp only [complexTorusPoint, add_sub_add_right_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
    rw [he] at hc
    have hc' : ‖E t z - E t w‖ ≤ (L : ℝ) * logFlowModulus ‖z - w‖ := by
      simpa only [E, ← map_sub, LinearIsometryEquiv.norm_map] using
        hc.trans (mul_le_mul_of_nonneg_left hm L.2)
    have hvps := velocityC_logFlowModulus_le (hωi t) (hωB t) (hωmass t) hzw
    have he' : v t z - v t w = (vp t z - vp t w) + (E t z - E t w) := by dsimp only [v]; abel
    rw [he']
    exact (norm_add_le _ _).trans ((add_le_add hvps hc').trans_eq (by
      simp only [CB, NNReal.coe_mk, B]; ring))
  have hvdiv (t : ℝ) : IsPlanarWeaklyDivergenceFree (fun x : R2 =>
      complexPhysicalPlane (v t (complexPhysicalPlane.symm x))) := by
    have hpct : Continuous (fun x : R2 => complexPhysicalPlane (vp t (complexPhysicalPlane.symm x))) :=
      complexPhysicalPlane.continuous.comp (Continuous.comp
        (f := fun x : R2 => (t, complexPhysicalPlane.symm x))
        (g := fun p : ℝ × ℂ => vp p.1 p.2) hvp
        (continuous_const.prodMk complexPhysicalPlane.symm.continuous))
    have hcct : Continuous (fun x : R2 => S.correctionLabelField t (x + torusCenter)) :=
      Continuous.comp (f := fun x : R2 => (t, x + torusCenter))
        (g := fun p : ℝ × R2 => S.correctionLabelField p.1 p.2)
        S.continuous_correctionLabelField (continuous_const.prodMk (continuous_id.add continuous_const))
    have he : (fun x : R2 => complexPhysicalPlane (v t (complexPhysicalPlane.symm x))) =
        (fun x : R2 => complexPhysicalPlane (vp t (complexPhysicalPlane.symm x)) +
          S.correctionLabelField t (x + torusCenter)) := by
      funext x
      simp only [v, E, map_add, LinearIsometryEquiv.apply_symm_apply, complexTorusPoint]
    rw [he]
    exact (isPlanarWeaklyDivergenceFree_velocityC (hωi t)
      (fun z => by simpa only [Real.norm_eq_abs] using hωB t z)).add
        (S.isPlanarWeaklyDivergenceFree_centeredCorrectionLabelField t) hpct hcct
  refine ⟨MB, CB, v, hv, ?_, hvM, hvlog, hvdiv⟩
  intro t ht z
  have hWt : W t = Z t := by
    dsimp only [W, Zi, τ]
    rw [projIcc_of_mem hD ht]
  simp only [v, vp, ω, hWt, E, complexPhysicalPlane_symm_eq_planeComplexEquiv]

theorem exists_finitePhase_actualCorrection_particleFlow_area
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D))
    (hphase : ∀ t ∈ Icc (0 : ℝ) D, ∃ b : ι → ℝ, ∀ i,
      ‖contourParameterShiftC1 (b i) (Z t i) - Z₀ i‖ < r i / 4) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) D, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (phaseFiniteContourPatchVorticity g (Z t)) (F t a) +
            planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (F t a)))) t) ∧
      ∀ t ∈ Icc (0 : ℝ) D, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume := by
  obtain ⟨M, C, v, hv, heq, hM, hlog, hdiv⟩ :=
    S.exists_finitePhase_actualCorrection_velocity g Z Z₀ r hr href hD hZ hphase
  obtain ⟨F, hFc, hFic, hF0, hFd, hFa⟩ :=
    exists_complex_measurePreserving_logHomeomorphFlow hv hM hlog hdiv hD
  refine ⟨F, hFc, hFic, hF0, ?_, hFa⟩
  intro t ht a
  simpa only [heq t ht] using hFd t ht a

end BoundedEulerParticleSystem
end Euler2D

end
