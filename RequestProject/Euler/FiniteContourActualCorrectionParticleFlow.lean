module

public import RequestProject.Euler.TorusParticleCorrectionIncompressibility
public import RequestProject.Euler.TorusHybridMaterialAgreementBounds
public import RequestProject.Euler.FiniteContourPlanarIncompressibility
public import RequestProject.Euler.WeakDivergenceHomeomorphFlow
public import RequestProject.Euler.ContourMaterialTransport
public import RequestProject.Euler.ActualTorusRemainderVelocity

/-! Genuine plane measure-preserving particles for the finite patch
velocity plus the correction of one fixed actual torus Euler system.
The physical center translation is retained in the actual equation. -/

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace Euler2D

namespace BoundedEulerParticleSystem

variable {f : Lp ℝ 2 μT} {T : ℝ} (S : BoundedEulerParticleSystem f T)

theorem exists_finiteContour_actualCorrection_particleFlow_area
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hD : 0 ≤ D)
    (hsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4)
    (hZ : ∀ i, ContinuousOn (fun t => Z t i) (Icc (0 : ℝ) D)) :
    ∃ F : ℝ → ℂ ≃ₜ ℂ,
      Continuous (fun p : ℝ × ℂ => F p.1 p.2) ∧
      Continuous (fun p : ℝ × ℂ => (F p.1).symm p.2) ∧
      (∀ a, F 0 a = a) ∧
      (∀ t ∈ Icc (0 : ℝ) D, ∀ a,
        HasDerivAt (fun s => F s a)
          (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) (F t a) +
            planeComplexEquiv (S.correctionLabelField t (complexTorusPoint (F t a)))) t) ∧
      ∀ t ∈ Icc (0 : ℝ) D, MeasurePreserving (F t) volume volume ∧
        MeasurePreserving (F t).symm volume volume := by
  let Zi : Icc (0 : ℝ) D → ι → ContourC1Space γ := fun t => Z t
  let hsmalli : ∀ t : Icc (0 : ℝ) D, ∀ i, ‖Zi t i - Z₀ i‖ ≤ r i / 4 :=
    fun t i => hsmall t t.property i
  have hZi (i : ι) : Continuous (fun t : Icc (0 : ℝ) D => Zi t i) := (hZ i).restrict
  let vp := finiteContourPlanarVelocity hD g Zi Z₀ r hr href hsmalli
  have hvp : Continuous (Function.uncurry vp) :=
    continuous_finiteContourPlanarVelocity hD g Zi Z₀ r hr href hsmalli hZi
  obtain ⟨M, hM, hMc⟩ := S.exists_uniform_bound_correctionLabelField
  obtain ⟨L, hL⟩ := S.exists_lipschitzWith_correctionLabelField
  let B : ℝ := finiteContourPatchSupBound g + finiteContourPatchMassBound g r
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  let MB : ℝ≥0 := NNReal.mk (B + M) (add_nonneg hB hM)
  let CB : ℝ≥0 := NNReal.mk (8 * B + L) (by positivity)
  let v : ℝ → R2 → R2 := fun t x => vp t x + S.correctionLabelField t (x + torusCenter)
  have hj : Continuous (fun p : ℝ × R2 => (p.1, p.2 + torusCenter)) :=
    continuous_fst.prodMk (continuous_snd.add continuous_const)
  have hcorr : Continuous (fun p : ℝ × R2 => S.correctionLabelField p.1 (p.2 + torusCenter)) :=
    Continuous.comp (f := fun p : ℝ × R2 => (p.1, p.2 + torusCenter))
      (g := fun p : ℝ × R2 => S.correctionLabelField p.1 p.2) S.continuous_correctionLabelField hj
  have hv : Continuous (Function.uncurry v) := hvp.add hcorr
  have hvM (t : ℝ) (x : R2) : ‖v t x‖ ≤ MB :=
    (norm_add_le _ _).trans (add_le_add
      (norm_finiteContourPlanarVelocity_le hD g Zi Z₀ r hr href hsmalli t x) (hMc t _))
  have hvlog (t : ℝ) (x y : R2) (hxy : ‖x - y‖ ≤ 1 / 2) :
      ‖v t x - v t y‖ ≤ CB * logFlowModulus ‖x - y‖ := by
    have hm : ‖x - y‖ ≤ logFlowModulus ‖x - y‖ := by
      have hl := Real.log_nonpos (norm_nonneg (x - y)) (hxy.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
      have hp := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (x - y)) hl
      dsimp only [logFlowModulus]
      linarith
    have hc := (hL t).dist_le_mul (x + torusCenter) (y + torusCenter)
    rw [dist_eq_norm, dist_eq_norm,
      show (x + torusCenter) - (y + torusCenter) = x - y by abel] at hc
    have he : v t x - v t y = (vp t x - vp t y) +
        (S.correctionLabelField t (x + torusCenter) - S.correctionLabelField t (y + torusCenter)) := by
      dsimp only [v]
      abel
    rw [he]
    calc
      _ ≤ ‖vp t x - vp t y‖ +
          ‖S.correctionLabelField t (x + torusCenter) - S.correctionLabelField t (y + torusCenter)‖ := norm_add_le _ _
      _ ≤ (8 * B) * logFlowModulus ‖x - y‖ + (L : ℝ) * logFlowModulus ‖x - y‖ :=
        add_le_add (finiteContourPlanarVelocity_logFlowModulus_le hD g Zi Z₀ r hr href hsmalli t hxy)
          (hc.trans (mul_le_mul_of_nonneg_left hm L.2))
      _ = _ := by simp only [CB, NNReal.coe_mk]; ring
  have hvdiv (t : ℝ) : IsPlanarWeaklyDivergenceFree (v t) := by
    have hpct : Continuous (fun x : R2 => vp t x) := Continuous.comp
      (f := fun x : R2 => (t, x)) (g := fun p : ℝ × R2 => vp p.1 p.2)
      hvp (continuous_const.prodMk continuous_id)
    have hcct : Continuous (fun x : R2 => S.correctionLabelField t (x + torusCenter)) := Continuous.comp
      (f := fun x : R2 => (t, x))
      (g := fun p : ℝ × R2 => S.correctionLabelField p.1 (p.2 + torusCenter))
      hcorr (continuous_const.prodMk continuous_id)
    exact (isPlanarWeaklyDivergenceFree_finiteContourPlanarVelocity hD g Zi Z₀ r hr href hsmalli t).add
      (S.isPlanarWeaklyDivergenceFree_centeredCorrectionLabelField t)
      hpct hcct
  let vc : ℝ → ℂ → ℂ := fun t z => complexPhysicalPlane.symm (v t (complexPhysicalPlane z))
  have hvrpull : Continuous (fun p : ℝ × ℂ => v p.1 (complexPhysicalPlane p.2)) := Continuous.comp
    (f := fun p : ℝ × ℂ => (p.1, complexPhysicalPlane p.2))
    (g := fun p : ℝ × R2 => v p.1 p.2) hv
    (continuous_fst.prodMk (complexPhysicalPlane.continuous.comp continuous_snd))
  have hvc : Continuous (Function.uncurry vc) := Continuous.comp
    (f := fun p : ℝ × ℂ => v p.1 (complexPhysicalPlane p.2))
    (g := fun x : R2 => complexPhysicalPlane.symm x) complexPhysicalPlane.symm.continuous hvrpull
  have hvcM (t : ℝ) (z : ℂ) : ‖vc t z‖ ≤ MB := by
    simpa only [vc, LinearIsometryEquiv.norm_map] using hvM t (complexPhysicalPlane z)
  have hvclog (t : ℝ) (z w : ℂ) (hzw : ‖z - w‖ ≤ 1 / 2) :
      ‖vc t z - vc t w‖ ≤ CB * logFlowModulus ‖z - w‖ := by
    have hh := hvlog t (complexPhysicalPlane z) (complexPhysicalPlane w)
      (by simpa only [← map_sub, LinearIsometryEquiv.norm_map] using hzw)
    simpa only [vc, ← map_sub, LinearIsometryEquiv.norm_map] using hh
  have hvcdiv (t : ℝ) : IsPlanarWeaklyDivergenceFree
      (fun x : R2 => complexPhysicalPlane (vc t (complexPhysicalPlane.symm x))) := by
    have he : (fun x : R2 => complexPhysicalPlane (vc t (complexPhysicalPlane.symm x))) = v t := by
      funext x
      simp only [vc, LinearIsometryEquiv.apply_symm_apply]
    rw [he]
    exact hvdiv t
  obtain ⟨F, hFc, hFic, hF0, hFd, hFarea⟩ :=
    exists_complex_measurePreserving_logHomeomorphFlow hvc hvcM hvclog hvcdiv hD
  refine ⟨F, hFc, hFic, hF0, ?_, hFarea⟩
  intro t ht a
  have hd := hFd t ht a
  have hp := finiteContourPlanarVelocity_apply hD g Zi Z₀ r hr href hsmalli
    (⟨t, ht⟩ : Icc (0 : ℝ) D) (F t a)
  change vp t (complexPhysicalPlane (F t a)) = _ at hp
  change HasDerivAt (fun s => F s a)
    (complexPhysicalPlane.symm (vp t (complexPhysicalPlane (F t a)) +
      S.correctionLabelField t (complexPhysicalPlane (F t a) + torusCenter))) t at hd
  rw [hp, map_add, LinearIsometryEquiv.symm_apply_apply] at hd
  simpa only [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht,
    complexPhysicalPlane_symm_eq_planeComplexEquiv, complexTorusPoint, Zi] using hd

theorem exists_finiteContour_actualCorrection_logBound
    {γ : ℝ≥0} {ι : Type*} [Fintype ι]
    (g : ι → ℝ) (Z : ℝ → ι → ContourC1Space γ) (Z₀ : ι → ContourC1Space γ)
    (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (href : ∀ i, ContourC1Space.lift γ (Z₀ i) = refCircle (r i))
    {D : ℝ} (hsmall : ∀ t ∈ Icc (0 : ℝ) D, ∀ i, ‖Z t i - Z₀ i‖ ≤ r i / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) D, ∀ x y : ℂ, ‖x - y‖ ≤ 1 / 2 →
      ‖(velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) x +
          planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x))) -
        (velocityC (finiteContourPatchVorticityOnInterval g Z Z₀ r hr href hsmall t) y +
          planeComplexEquiv (S.correctionLabelField t (complexTorusPoint y)))‖ ≤
          C * logFlowModulus ‖x - y‖ := by
  obtain ⟨L, hL⟩ := S.exists_lipschitzWith_correctionLabelField
  let B := finiteContourPatchSupBound g + finiteContourPatchMassBound g r
  have hB : 0 ≤ B := by
    dsimp only [B]
    unfold finiteContourPatchSupBound finiteContourPatchMassBound contourPatchMassBound
    positivity
  refine ⟨8 * B + L, by positivity, ?_⟩
  intro t ht x y hxy
  have hm : ‖x - y‖ ≤ logFlowModulus ‖x - y‖ := by
    have hp := mul_nonpos_of_nonneg_of_nonpos (norm_nonneg (x - y))
      (Real.log_nonpos (norm_nonneg _) (hxy.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)))
    dsimp only [logFlowModulus]
    linarith
  have hc := (hL t).dist_le_mul (complexTorusPoint x) (complexTorusPoint y)
  rw [dist_eq_norm, dist_eq_norm] at hc
  have he : ‖complexTorusPoint x - complexTorusPoint y‖ = ‖x - y‖ := by
    simp only [complexTorusPoint, add_sub_add_right_eq_sub, ← map_sub, LinearIsometryEquiv.norm_map]
  rw [he] at hc
  have hc' : ‖planeComplexEquiv (S.correctionLabelField t (complexTorusPoint x)) -
      planeComplexEquiv (S.correctionLabelField t (complexTorusPoint y))‖ ≤
      (L : ℝ) * logFlowModulus ‖x - y‖ := by
    simpa only [← complexPhysicalPlane_symm_eq_planeComplexEquiv, ← map_sub,
      LinearIsometryEquiv.norm_map] using hc.trans (mul_le_mul_of_nonneg_left hm L.2)
  rw [finiteContourPatchVorticityOnInterval_of_mem g Z Z₀ r hr href hsmall ht]
  have hsplit (a b c d : ℂ) : (a + b) - (c + d) = (a - c) + (b - d) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ (8 * B) * logFlowModulus ‖x - y‖ + (L : ℝ) * logFlowModulus ‖x - y‖ :=
      add_le_add (finiteContourPatchVelocity_logFlowModulus_le g (Z t) Z₀ r hr href (hsmall t ht) hxy) hc'
    _ = _ := by ring

end BoundedEulerParticleSystem
end Euler2D

end
