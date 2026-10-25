module

public import RequestProject.Euler.Delay
public import RequestProject.Euler.CircularActualLimitSolution

/-!
# The principal statements

* `limit_solution` — **Proposition `cp:limit`** (*Limit solution*), in the form used by the
  paper's proof of the main theorem: for every `T > 0` and `1 < p < ∞` there is a mean-zero,
  divergence-free, *stationary* datum `u₀ ∈ W^{1,p}` and a weak Euler solution `u` from `u₀`
  with vorticity in `L^∞(0,T;Lᵖ)` that departs from `u₀` at some time `t* ∈ (0,T)`.
  Its proof uses the actual finite vortex-patch solutions, normal hyperbolicity,
  the Laplace-transform transfer, uniform velocity departure and compactness,
  assembled in `circular_actual_limit_solution`.
* `main_nonuniqueness` — **Theorem `main`**, proved here from `limit_solution` exactly as in
  the paper: the two solutions are `u` and the stationary solution `t ↦ u₀`.
* `refinement_uncountable` — **Corollary `intro:refinement`** (without the energy and
  `W^{1,∞}(0,T;L²)` statements), proved from `limit_solution` via the delayed solutions of
  Proposition `cp:prop:delays` (`delayed_family`).
-/

@[expose] public section

open MeasureTheory Real Filter Topology Set
open scoped ContDiff

namespace Euler2D

lemma memLp_mul_test_integrable {p : ENNReal} (hp : 1 ≤ p) {g : R2 → ℝ} (hg : MemLp g p μT)
    {ψ : R2 → ℝ} (hψ : Continuous ψ) : Integrable (fun x => g x * ψ x) μT := by
  obtain ⟨C, hC⟩ := bound_on_box hψ
  refine (hg.integrable hp).mul_bdd (c := C) hψ.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_torusBox]
  exact Eventually.of_forall fun x hx => by simpa [Real.norm_eq_abs] using hC x hx

/-- A `W^{1,p}` field (`p ≥ 1`) has an `Lᵖ` curl; hence the constant path has bounded
vorticity. -/
lemma MemW1p.curlBounded_const {p : ENNReal} (hp : 1 ≤ p) {u₀ : L2T} (h : MemW1p p u₀)
    (T : ℝ) : CurlBounded T p (fun _ => u₀) := by
  obtain ⟨-, G, hG, hGu⟩ := h
  set w : R2 → ℝ := fun x => G 0 1 x - G 1 0 x
  have hw : MemLp w p μT := (hG 0 1).sub (hG 1 0)
  refine ⟨(eLpNorm w p μT).toReal, fun _ _ => ⟨w, hw, fun ψ hψ => ?_, le_rfl⟩⟩
  have hψc : Continuous ψ := hψ.1.continuous
  have hpd : ∀ i, Continuous (pd i ψ) := fun i =>
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have Iu : ∀ i j, Integrable (fun x => u₀ x j * pd i ψ x) μT := fun i j => by
    obtain ⟨C, hC⟩ := bound_on_box (hpd i)
    exact integrable_lin u₀ j (hpd i).aestronglyMeasurable hC
  simp only [w, sub_mul]
  rw [integral_sub (memLp_mul_test_integrable hp (hG 0 1) hψc)
    (memLp_mul_test_integrable hp (hG 1 0) hψc), integral_sub (Iu 1 0) (Iu 0 1),
    hGu 1 0 ψ hψ, hGu 0 1 ψ hψ]
  ring

/-- **Proposition (Limit solution, `cp:limit`).**  For every `T > 0` and `1 < p < ∞` there is
a mean-zero, divergence-free, stationary datum `u₀ ∈ L² ∩ W^{1,p}` and a weak Euler solution `u`
with `u(0) = u₀`, `curl u ∈ L^∞(0,T;Lᵖ)`, and `u(t*) ≠ u₀` for some `t* ∈ (0,T)`.

The proof obtains `u` as a limit of the actual finite vortex-patch solutions,
with uniform curl bounds and a fixed positive velocity departure. -/
theorem limit_solution (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 < p) :
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧ MemW1p (ENNReal.ofReal p) u₀ ∧
      IsStationary u₀ ∧
      ∃ u : ℝ → L2T, IsWeakEulerSolution T u₀ u ∧ CurlBounded T (ENNReal.ofReal p) u ∧
        ∃ tstar ∈ Ioo 0 T, u tstar ≠ u₀ := by
  exact circular_actual_limit_solution (γ := (1 / 2 : NNReal))
    (by norm_num) (by norm_num) T hT p hp

/-- **Theorem (main).** For every `T > 0` and `1 < p < ∞` there is a mean-zero,
divergence-free `u₀ ∈ L² ∩ W^{1,p}` with two weak Euler solutions `u⁽¹⁾, u⁽²⁾` whose
vorticities lie in `L^∞(0,T;Lᵖ)` and which differ in `L²((0,T)×𝕋²)`.

Proved from Proposition `cp:limit` (`limit_solution`), as in the paper. -/
theorem main_nonuniqueness (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 < p) :
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧ MemW1p (ENNReal.ofReal p) u₀ ∧
      ∃ u₁ u₂ : ℝ → L2T,
        IsWeakEulerSolution T u₀ u₁ ∧ IsWeakEulerSolution T u₀ u₂ ∧
        CurlBounded T (ENNReal.ofReal p) u₁ ∧ CurlBounded T (ENNReal.ofReal p) u₂ ∧
        0 < spaceTimeDistSq T u₁ u₂ := by
  obtain ⟨u₀, hmean, hdiv, hW, hs, u, hu, hc, tstar, ht, hne⟩ := limit_solution T hT p hp
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  refine ⟨u₀, hmean, hdiv, hW, u, fun _ => u₀, hu, stationary_isWeakSolution hdiv hs, hc,
    hW.curlBounded_const hp1 T, ?_⟩
  exact spaceTimeDistSq_pos hu.continuous continuousOn_const ht hne

/-- **Corollary (refinement, `intro:refinement`)**, without the energy and `W^{1,∞}(0,T;L²)`
statements: the datum of the main theorem admits an uncountable family of pairwise distinct
(in `L²((0,T)×𝕋²)`) weak solutions, all with the same vorticity bound.

Proved from Proposition `cp:limit` by the delayed-solution argument (`delayed_family`). -/
theorem refinement_uncountable (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 1 < p) :
    ∃ u₀ : L2T, (∫ x in torusBox, u₀ x = 0) ∧ DivFree u₀ ∧ MemW1p (ENNReal.ofReal p) u₀ ∧
      ∃ M : ℝ, ∃ S : Set ℝ, ¬ S.Countable ∧ ∃ U : ℝ → ℝ → L2T,
        (∀ θ ∈ S, IsWeakEulerSolution T u₀ (U θ) ∧ CurlBoundedBy T (ENNReal.ofReal p) M (U θ)) ∧
        ∀ θ₁ ∈ S, ∀ θ₂ ∈ S, θ₁ ≠ θ₂ → 0 < spaceTimeDistSq T (U θ₁) (U θ₂) := by
  obtain ⟨u₀, hmean, hdiv, hW, hs, u, hu, ⟨M, hc⟩, tstar, ht, hne⟩ := limit_solution T hT p hp
  exact ⟨u₀, hmean, hdiv, hW, M, delayed_family hT hs hu hc ht hne⟩

end Euler2D

end
