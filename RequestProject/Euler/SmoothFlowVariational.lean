module

public import RequestProject.Euler.SmoothFlowEstimates
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Actual existence for the variational equation

A compactly supported smooth cutoff first makes the linear operator ODE
globally bounded. Grönwall's inequality then proves that the actual solution
stays inside the region where the cutoff is the identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ContDiff

namespace Euler2D

theorem exists_boundedODE_continuous_curve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {K M : ℝ≥0}
    (hfc : Continuous (Function.uncurry f)) (hfL : ∀ t, LipschitzWith K (f t))
    (hfM : ∀ t x, ‖f t x‖ ≤ M) {T : ℝ} (hT : 0 ≤ T) (a : E) :
    ∃ α : ℝ → E, Continuous α ∧ α 0 = a ∧
      ∀ t ∈ Ioo (-1 : ℝ) (T + 1), HasDerivAt α (f t (α t)) t := by
  have hp : IsPicardLindelof f
      (⟨0, by norm_num, by linarith⟩ : Icc (-1 : ℝ) (T + 1)) a
      (M * NNReal.mk (T + 2) (by linarith)) 0 M K := by
    refine ⟨fun t ht => (hfL t).lipschitzOnWith, ?_, fun t ht x hx => hfM t x, ?_⟩
    · intro x hx
      exact (hfc.comp (continuous_id.prodMk continuous_const)).continuousOn
    · have hh : max (T + 1 - (0 : ℝ)) (0 - -1) ≤ T + 2 := max_le (by linarith) (by linarith)
      change (M : ℝ) * max (T + 1 - (0 : ℝ)) (0 - -1) ≤ (M : ℝ) * (T + 2) - 0
      calc
        _ ≤ (M : ℝ) * (T + 2) := mul_le_mul_of_nonneg_left hh M.2
        _ = _ := (sub_zero _).symm
  obtain ⟨α, hα0, hαd⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  let β : ℝ → E := fun t => α (particleTimeClamp hT t)
  have hβ (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) (T + 1)) : β t = α t := by
    simp only [β, particleTimeClamp, projIcc_of_mem _ ht]
  refine ⟨β, (HasDerivWithinAt.continuousOn hαd).restrict.comp
      (continuous_projIcc (h := by linarith)), ?_, ?_⟩
  · rw [hβ 0 ⟨by norm_num, by linarith⟩]
    exact hα0
  · intro t ht
    have htJ : Icc (-1 : ℝ) (T + 1) ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have heq : β =ᶠ[𝓝 t] α := by
      filter_upwards [htJ] with u hu
      exact hβ u hu
    have hd := (hαd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt htJ
    simpa only [hβ t ⟨ht.1.le, ht.2.le⟩] using hd.congr_of_eventuallyEq heq

theorem exists_variational_curve {B : ℝ → R2 →L[ℝ] R2} {K : ℝ≥0}
    (hBc : Continuous B) (hB : ∀ t, ‖B t‖ ≤ K) {T : ℝ} (hT : 0 ≤ T) :
    ∃ A : ℝ → R2 →L[ℝ] R2, Continuous A ∧ A 0 = ContinuousLinearMap.id ℝ R2 ∧
      (∀ t ∈ Icc (0 : ℝ) T, HasDerivAt A ((B t).comp (A t)) t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ Real.exp ((K : ℝ) * t) := by
  let E := R2 →L[ℝ] R2
  let R : ℝ := 2 * Real.exp ((K : ℝ) * T)
  have hR : 0 < R := by positivity
  let b : ContDiffBump (0 : E) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := by linarith }
  let G : E → E := fun C => b C • C
  have hGc : ContDiff ℝ 1 G := b.contDiff.smul contDiff_id
  have hGcs : HasCompactSupport G :=
    b.hasCompactSupport.smul_right (f' := fun C : E => C)
  obtain ⟨L, hGL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hGcs hGc one_ne_zero
  have hGn (C : E) : ‖G C‖ ≤ ‖C‖ := by
    calc
      ‖G C‖ = b C * ‖C‖ := by simp only [G, norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
      _ ≤ 1 * ‖C‖ := mul_le_mul_of_nonneg_right b.le_one (norm_nonneg _)
      _ = ‖C‖ := one_mul _
  have hGb (C : E) : ‖G C‖ ≤ R + 1 := by
    by_cases hC : ‖C‖ < R + 1
    · exact (hGn C).trans hC.le
    · have hz : b C = 0 := b.zero_of_le_dist (by simpa only [dist_zero_right] using le_of_not_gt hC)
      change ‖(b C : ℝ) • C‖ ≤ R + 1
      rw [norm_smul, Real.norm_eq_abs, hz, abs_zero, zero_mul]
      linarith
  let f : ℝ → E → E := fun t C => (B t).comp (G C)
  have hfc : Continuous (Function.uncurry f) :=
    (hBc.comp continuous_fst).clm_comp (hGc.continuous.comp continuous_snd)
  have hfL : ∀ t, LipschitzWith (K * L) (f t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro C D
    change dist ((B t).comp (G C)) ((B t).comp (G D)) ≤ _
    rw [dist_eq_norm, ← ContinuousLinearMap.comp_sub]
    calc
      ‖(B t).comp (G C - G D)‖ ≤ ‖B t‖ * ‖G C - G D‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K : ℝ) * ((L : ℝ) * dist C D) :=
        mul_le_mul (hB t) (by
          rw [← dist_eq_norm]
          exact hGL.dist_le_mul C D)
          (norm_nonneg _) K.2
      _ = _ := by simp only [NNReal.coe_mul]; ring
  have hfM : ∀ t C, ‖f t C‖ ≤ (K * NNReal.mk (R + 1) (by linarith) : ℝ≥0) := by
    intro t C
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hB t) (hGb C) (norm_nonneg _) K.2)
  letI : CompleteSpace R2 := PiLp.completeSpace (p := 2) (β := fun _ : Fin 2 => ℝ)
  letI : CompleteSpace E :=
    ContinuousLinearMap.instCompleteSpace (σ := RingHom.id ℝ) (E := R2) (F := R2)
  obtain ⟨A, hAc, hA0, hAd⟩ := exists_boundedODE_continuous_curve
    (E := E) (f := f) (K := K * L) (M := K * NNReal.mk (R + 1) (by linarith))
    hfc hfL hfM hT (ContinuousLinearMap.id ℝ R2)
  have hgrowth (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖A t‖ ≤ Real.exp ((K : ℝ) * t) := by
    have hd := norm_le_gronwallBound_of_norm_deriv_right_le hAc.continuousOn
      (fun u hu => (hAd u (by constructor <;> linarith [hu.1, hu.2, ht.2])).hasDerivWithinAt)
      (a := (0 : ℝ)) (b := t) (δ := 1) (ε := 0) (K := (K : ℝ))
      (by rw [hA0]; exact ContinuousLinearMap.norm_id_le)
      (fun u hu => by
        change ‖(B u).comp (G (A u))‖ ≤ _
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (by simpa only [add_zero] using mul_le_mul (hB u) (hGn (A u)) (norm_nonneg _) K.2))
      t ⟨ht.1, le_rfl⟩
    simpa only [gronwallBound_ε0, one_mul, sub_zero] using hd
  refine ⟨A, hAc, hA0, ?_, hgrowth⟩
  intro t ht
  have hAt : ‖A t‖ ≤ R := by
    have hexp : Real.exp ((K : ℝ) * t) ≤ Real.exp ((K : ℝ) * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.2)
    exact (hgrowth t ht).trans (hexp.trans (by dsimp [R]; linarith [Real.exp_pos ((K : ℝ) * T)]))
  have hGone : G (A t) = A t := by
    change b (A t) • A t = A t
    rw [b.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using hAt), one_smul]
  simpa only [f, hGone] using hAd t (by constructor <;> linarith [ht.1, ht.2])

end Euler2D

end
