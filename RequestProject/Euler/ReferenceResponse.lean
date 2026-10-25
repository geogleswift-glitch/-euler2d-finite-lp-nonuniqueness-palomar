module

public import Mathlib

/-!
# The reference response (Lemma `re:lem:reference`)

Let `X` be a real Banach space (the parent's fixed-area tangent space), `U(s,t) : X → X` the
circular-reference evolution operators, `𝓑(t) : ℂ → X` the real-linear forcing operators and
`ℓ(s) : X → ℂ` the growing-coordinate functionals. The paper's Definition `re:def:data` gives
`‖U(s,t)‖ ≤ M e^{bσ(s−t)}` for `s ≥ t`, `ℓ(s) U(s,t) = e^{bλ_*(s−t)} ℓ(t)` and
`ℓ(t) 𝓑(t)[z] = K_* z`, where `λ_* = σ − 3i/4`, and the canonical fourth moment satisfies
`|N(t)| ≤ C e^{σt}` for `t ≤ 0` and `|N(t)| ≤ C(1+t)⁴` for `t ≥ 0`.

* `reference_response_integrable`: the integrand `U(s,t) 𝓑(t)[e^{-2ibt} N(t)]` is integrable on
  `(−∞, s]` (absolute convergence of the Bochner integral `Y_χ(s)`).
* `reference_response_growing`: `ℓ(s) Y_χ(s) = K_* e^{bλ_* s} ∫_{−∞}^s e^{−b(σ+5i/4)t} N(t) dt`.
* `fourth_moment_rotation`: rotating the cell by a fixed angle `ϑ` multiplies its fourth moment
  `∫ \bar z⁴ Ω` by `e^{−4iϑ}`; hence the scalar response is multiplied by `e^{−4iϑ}`
  (`reference_response_rotation`).

Measurability of the integrand in `t` is taken as a hypothesis (the paper uses continuity).
-/

@[expose] public section

open MeasureTheory Complex Set Real ComplexConjugate

namespace Euler2D

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- `λ_* = σ − 3i/4` with `σ = 9√15/100`. -/
noncomputable def lambdaStar (σ : ℝ) : ℂ := σ - 3 / 4 * I

/-- The integrand of `Y_χ(s)`. -/
noncomputable def responseIntegrand (U : ℝ → ℝ → X →L[ℝ] X) (B : ℝ → ℂ →L[ℝ] X) (N : ℝ → ℂ)
    (b s t : ℝ) : X :=
  U s t (B t (exp (-(2 * b * t : ℝ) * I) * N t))

omit [CompleteSpace X] in
/-- Absolute convergence of the Bochner integral defining `Y_χ(s)`. -/
theorem reference_response_integrable {U : ℝ → ℝ → X →L[ℝ] X} {B : ℝ → ℂ →L[ℝ] X} {N : ℝ → ℂ}
    {b σ M CB C s : ℝ} (hb : b < 1) (hσ : 0 < σ)
    (hU : ∀ s t, t ≤ s → ‖U s t‖ ≤ M * Real.exp (b * σ * (s - t)))
    (hB : ∀ t, ‖B t‖ ≤ CB)
    (hNneg : ∀ t ≤ 0, ‖N t‖ ≤ C * Real.exp (σ * t))
    (hNpos : ∀ t, 0 ≤ t → ‖N t‖ ≤ C * (1 + t) ^ 4)
    (hmeas : AEStronglyMeasurable (responseIntegrand U B N b s) (volume.restrict (Iic s))) :
    IntegrableOn (responseIntegrand U B N b s) (Iic s) := by
  have hM : 0 ≤ M := by
    have := (norm_nonneg _).trans (hU s s le_rfl)
    simpa using this
  have hCB : 0 ≤ CB := (norm_nonneg _).trans (hB 0)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hNneg 0 le_rfl)
    simpa using this
  have hnormE : ∀ t : ℝ, ‖exp (-(2 * b * t : ℝ) * I)‖ = 1 := by
    intro t
    rw [show -((2 * b * t : ℝ) : ℂ) * I = ((-(2 * b * t) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hbound : ∀ t, t ≤ s → ‖responseIntegrand U B N b s t‖ ≤
      M * Real.exp (b * σ * (s - t)) * CB * ‖N t‖ := by
    intro t ht
    simp only [responseIntegrand]
    calc ‖U s t (B t (exp (-(2 * b * t : ℝ) * I) * N t))‖
        ≤ ‖U s t‖ * (‖B t‖ * ‖exp (-(2 * b * t : ℝ) * I) * N t‖) :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ (M * Real.exp (b * σ * (s - t))) * (CB * ‖N t‖) := by
          rw [norm_mul, hnormE, one_mul]
          exact mul_le_mul (hU s t ht) (mul_le_mul_of_nonneg_right (hB t) (norm_nonneg _))
            (by positivity) (by positivity)
      _ = _ := by ring
  set s0 := min s 0 with hs0
  have hsplit : Iic s = Iic s0 ∪ Icc s0 s := by
    rw [Iic_union_Icc_eq_Iic (min_le_left _ _)]
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hsub : Iic s0 ⊆ Iic s := Iic_subset_Iic.mpr (min_le_left _ _)
    have hk : 0 < (1 - b) * σ := mul_pos (by linarith) hσ
    refine Integrable.mono' (((integrableOn_exp_mul_Iic hk s0).const_mul
      (M * Real.exp (b * σ * s) * CB * C))) (hmeas.mono_measure (Measure.restrict_mono hsub le_rfl))
      ((ae_restrict_mem measurableSet_Iic).mono fun t ht => ?_)
    have ht0 : t ≤ 0 := ht.trans (min_le_right _ _)
    have hts : t ≤ s := ht.trans (min_le_left _ _)
    refine (hbound t hts).trans ?_
    have h1 := hNneg t ht0
    calc M * Real.exp (b * σ * (s - t)) * CB * ‖N t‖
        ≤ M * Real.exp (b * σ * (s - t)) * CB * (C * Real.exp (σ * t)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = M * Real.exp (b * σ * s) * CB * C * Real.exp ((1 - b) * σ * t) := by
          have : Real.exp (b * σ * (s - t)) * Real.exp (σ * t) =
              Real.exp (b * σ * s) * Real.exp ((1 - b) * σ * t) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (M * CB * C) * this
  · have hsub : Icc s0 s ⊆ Iic s := fun t ht => ht.2
    refine Integrable.mono' (integrableOn_const (C := M * Real.exp (|b| * σ * (s - s0)) * CB *
      (C + C * (1 + |s|) ^ 4)) (by simp) enorm_ne_top)
      (hmeas.mono_measure (Measure.restrict_mono hsub le_rfl))
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht => ?_)
    refine (hbound t ht.2).trans ?_
    have hN : ‖N t‖ ≤ C + C * (1 + |s|) ^ 4 := by
      rcases le_or_gt t 0 with h0 | h0
      · have := hNneg t h0
        have : Real.exp (σ * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        nlinarith [mul_nonneg hC (pow_nonneg (by positivity : (0 : ℝ) ≤ 1 + |s|) 4)]
      · have h1 := hNpos t h0.le
        have h2 : (1 + t) ^ 4 ≤ (1 + |s|) ^ 4 :=
          pow_le_pow_left₀ (by linarith) (by linarith [ht.2, le_abs_self s]) 4
        nlinarith [mul_le_mul_of_nonneg_left h2 hC]
    have hE : Real.exp (b * σ * (s - t)) ≤ Real.exp (|b| * σ * (s - s0)) := by
      apply Real.exp_le_exp.mpr
      have h1 : 0 ≤ s - t := by linarith [ht.2]
      have h2 : s - t ≤ s - s0 := by linarith [ht.1]
      calc b * σ * (s - t) ≤ |b| * σ * (s - t) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self b) hσ.le) h1
        _ ≤ |b| * σ * (s - s0) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have := mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hM) hCB) hN
      (norm_nonneg _) (by positivity)
    exact this

/-- The growing coordinate of the reference response:
`ℓ(s) Y_χ(s) = K_* e^{bλ_* s} ∫_{−∞}^s e^{−b(σ+5i/4)t} N(t) dt`. -/
theorem reference_response_growing {U : ℝ → ℝ → X →L[ℝ] X} {B : ℝ → ℂ →L[ℝ] X} {N : ℝ → ℂ}
    {ℓ : ℝ → X →L[ℝ] ℂ} {b σ s : ℝ} {K : ℂ}
    (hℓU : ∀ s t x, t ≤ s → ℓ s (U s t x) = exp ((b * (s - t) : ℝ) * lambdaStar σ) * ℓ t x)
    (hℓB : ∀ t z, ℓ t (B t z) = K * z)
    (hint : IntegrableOn (responseIntegrand U B N b s) (Iic s)) :
    ℓ s (∫ t in Iic s, responseIntegrand U B N b s t) =
      K * exp ((b * s : ℝ) * lambdaStar σ) *
        ∫ t in Iic s, exp (-((b * t : ℝ) * (σ + 5 / 4 * I))) * N t := by
  rw [← ContinuousLinearMap.integral_comp_comm _ hint, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Iic fun t ht => ?_
  simp only [responseIntegrand]
  rw [hℓU s t _ ht, hℓB]
  have hexp : exp ((b * (s - t) : ℝ) * lambdaStar σ) * exp (-(2 * b * t : ℝ) * I) =
      exp ((b * s : ℝ) * lambdaStar σ) * exp (-((b * t : ℝ) * (σ + 5 / 4 * I))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [lambdaStar]
    push_cast; ring
  linear_combination (K * N t) * hexp

/-- Rotating a density by a fixed angle `ϑ` multiplies its fourth moment `∫ \bar z⁴ Ω` by
`e^{−4iϑ}`. -/
theorem fourth_moment_rotation (Ω : ℂ → ℝ) (ϑ : ℝ) :
    ∫ z, conj z ^ 4 * (Ω (exp (-(ϑ * I)) * z) : ℂ) =
      exp (-(4 * ϑ * I)) * ∫ z, conj z ^ 4 * (Ω z : ℂ) := by
  set a : Circle := Circle.exp (-ϑ) with ha
  have hac : (a : ℂ) = exp (-(ϑ * I)) := by
    rw [ha, Circle.coe_exp]; push_cast; ring_nf
  set G : ℂ → ℂ := fun w => conj (exp (ϑ * I) * w) ^ 4 * (Ω w : ℂ) with hG
  have hGa : ∀ z, G (rotation a z) = conj z ^ 4 * (Ω (exp (-(ϑ * I)) * z) : ℂ) := by
    intro z
    simp only [hG, rotation_apply, hac, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
      Complex.exp_zero, one_mul]
  have hGw : ∀ w, G w = exp (-(4 * ϑ * I)) * (conj w ^ 4 * (Ω w : ℂ)) := by
    intro w
    simp only [hG, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    rw [mul_pow, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hmp := (rotation a).measurePreserving
  have h := hmp.integral_comp (rotation a).toHomeomorph.measurableEmbedding G
  simp only [hGa, hGw] at h
  rw [h, integral_const_mul]

/-- Consequently the scalar response `∫_{−∞}^s e^{−b(σ+5i/4)t} N(t) dt` is multiplied by
`e^{−4iϑ}` when `N` is. -/
theorem reference_response_rotation (N : ℝ → ℂ) (b σ s ϑ : ℝ) :
    ∫ t in Iic s, exp (-((b * t : ℝ) * (σ + 5 / 4 * I))) * (exp (-(4 * ϑ * I)) * N t) =
      exp (-(4 * ϑ * I)) * ∫ t in Iic s, exp (-((b * t : ℝ) * (σ + 5 / 4 * I))) * N t := by
  simp_rw [mul_left_comm _ (exp (-(4 * ϑ * I)))]
  exact integral_const_mul _ _

end Euler2D
