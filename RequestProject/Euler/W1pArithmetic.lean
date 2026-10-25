module

public import RequestProject.Euler.RadialSobolev

/-!
# Arithmetic of quantitative Sobolev bounds

The original distributional derivative identities are stable under finite
sums, retaining the sum of the quantitative bounds.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Euler2D

lemma integrable_memLp_mul_continuous_torus {q : ENNReal} (hq : 1 ≤ q)
    {g ψ : R2 → ℝ} (hg : MemLp g q μT) (hψ : Continuous ψ) :
    Integrable (fun x => g x * ψ x) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hψ
  apply (hg.integrable hq).mul_bdd (c := C) hψ.aestronglyMeasurable
  rw [ae_restrict_iff' measurableSet_torusBox]
  exact Eventually.of_forall fun x hx => by simpa only [Real.norm_eq_abs] using hC x hx

lemma W1pBoundedBy.mono {q : ENNReal} {M N : ℝ} {u : R2 → R2}
    (h : W1pBoundedBy q M u) (hMN : M ≤ N) : W1pBoundedBy q N u := by
  obtain ⟨humem, hubound, G, hG, hGtest⟩ := h
  exact ⟨humem, hubound.trans (ENNReal.ofReal_le_ofReal hMN), G,
    fun i j => ⟨(hG i j).1, (hG i j).2.trans (ENNReal.ofReal_le_ofReal hMN)⟩, hGtest⟩

lemma W1pBoundedBy.zero (q : ENNReal) : W1pBoundedBy q 0 (fun _ : R2 => (0 : R2)) := by
  refine ⟨MemLp.zero', by simp, fun _ _ _ => 0, fun _ _ => ⟨MemLp.zero', by simp⟩, ?_⟩
  intro i j ψ hψ
  simp

lemma W1pBoundedBy.add {q : ENNReal} (hq : 1 ≤ q) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) {u v : R2 → R2}
    (hu : W1pBoundedBy q M u) (hv : W1pBoundedBy q N v) :
    W1pBoundedBy q (M + N) (fun x => u x + v x) := by
  obtain ⟨humem, hubound, G, hG, hGtest⟩ := hu
  obtain ⟨hvmem, hvbound, H, hH, hHtest⟩ := hv
  have hnorm {F : Type} [NormedAddCommGroup F] {f g : R2 → F}
      (hf : MemLp f q μT) (hg : MemLp g q μT)
      (hfb : eLpNorm f q μT ≤ ENNReal.ofReal M)
      (hgb : eLpNorm g q μT ≤ ENNReal.ofReal N) :
      eLpNorm (fun x => f x + g x) q μT ≤ ENNReal.ofReal (M + N) := by
    calc
      eLpNorm (fun x => f x + g x) q μT ≤ eLpNorm f q μT + eLpNorm g q μT :=
        eLpNorm_add_le hf.1 hg.1 hq
      _ ≤ ENNReal.ofReal M + ENNReal.ofReal N := add_le_add hfb hgb
      _ = ENNReal.ofReal (M + N) := (ENNReal.ofReal_add hM hN).symm
  have huv_mem : MemLp (fun x => u x + v x) q μT := humem.add hvmem
  have huv_bound : eLpNorm (fun x => u x + v x) q μT ≤ ENNReal.ofReal (M + N) :=
    hnorm (F := R2) humem hvmem hubound hvbound
  have hGH (i j : Fin 2) :
      MemLp (fun x => G i j x + H i j x) q μT ∧
        eLpNorm (fun x => G i j x + H i j x) q μT ≤ ENNReal.ofReal (M + N) := by
    exact ⟨(hG i j).1.add (hH i j).1,
      hnorm (F := ℝ) (hG i j).1 (hH i j).1 (hG i j).2 (hH i j).2⟩
  refine ⟨huv_mem, huv_bound, fun i j x => G i j x + H i j x, hGH, ?_⟩
  intro i j ψ hψ
  have hpd : Continuous (pd i ψ) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have Iu : Integrable (fun x => u x j * pd i ψ x) μT :=
    integrable_memLp_mul_continuous_torus hq
      (humem.continuousLinearMap_comp (EuclideanSpace.proj j : R2 →L[ℝ] ℝ)) hpd
  have Iv : Integrable (fun x => v x j * pd i ψ x) μT :=
    integrable_memLp_mul_continuous_torus hq
      (hvmem.continuousLinearMap_comp (EuclideanSpace.proj j : R2 →L[ℝ] ℝ)) hpd
  have IG : Integrable (fun x => G i j x * ψ x) μT :=
    integrable_memLp_mul_continuous_torus hq (hG i j).1 hψ.1.continuous
  have IH : Integrable (fun x => H i j x * ψ x) μT :=
    integrable_memLp_mul_continuous_torus hq (hH i j).1 hψ.1.continuous
  simp only [PiLp.add_apply, add_mul]
  rw [integral_add Iu Iv, integral_add IG IH, hGtest i j ψ hψ, hHtest i j ψ hψ]
  ring

lemma w1pBoundedBy_sum_range {q : ENNReal} (hq : 1 ≤ q)
    (M : ℕ → ℝ) (u : ℕ → R2 → R2) (hM : ∀ j, 0 ≤ M j)
    (hu : ∀ j, W1pBoundedBy q (M j) (u j)) (N : ℕ) :
    W1pBoundedBy q (∑ j ∈ Finset.range N, M j)
      (fun x => ∑ j ∈ Finset.range N, u j x) := by
  induction N with
  | zero => simpa using W1pBoundedBy.zero q
  | succ N ih =>
      simpa only [Finset.sum_range_succ] using
        W1pBoundedBy.add hq (Finset.sum_nonneg fun j _ => hM j) (hM N) ih (hu N)

end Euler2D

end
