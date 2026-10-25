module

public import Mathlib

/-!
# The fixed-area chart (Lemma `pc:area-chart`)

Loops are `2π`-periodic `C¹` maps `z : ℝ → ℂ`. Their signed area is
`𝒜(z) = ½ ∫_0^{2π} (z¹ (z²)' − z² (z¹)') dθ = ½ ∫_0^{2π} Im(\bar z z') dθ` (`loopArea`).
For the reference circle `z⁰(θ) = d e^{iθ}` put
`ℓ(v) = d ∫_0^{2π} Re(e^{-iθ} v(θ)) dθ` (`ellFun`), `c(v) = √(1 − 𝒜(v)/(πd²)) − 1` (`chartCoeff`)
and `Ξ(v) = (1 + c(v)) z⁰ + v` (`areaChart`).

* `loopArea_affine`: `𝒜(b z⁰ + v) = b² π d² + b ℓ(v) + 𝒜(v)` (the quadratic identity).
* `loopArea_areaChart`: if `ℓ(v) = 0` and `𝒜(v) ≤ π d²`, then `𝒜(Ξ(v)) = π d²`.
* `chart_coeff_unique`: conversely, if `z = (1 + t) z⁰ + v` with `ℓ(v) = 0`, `1 + t > 0` and
  `𝒜(z) = π d²`, then `t = c(v)`, i.e. `z = Ξ(v)`; and the decomposition exists with
  `t = ℓ(z − z⁰)/(2π d²)` (`chart_decomposition`).
* `areaChart_equivariant`: `Ξ(G_ϑ v) = G_ϑ Ξ(v)` for `(G_ϑ z)(θ) = e^{iϑ} z(θ − ϑ)`, together
  with the invariance of `ℓ` and `𝒜` under `G_ϑ`.

The analyticity of `Ξ` and `DΞ(0) = I` in the little-Hölder space are not formalized.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Set Real intervalIntegral

namespace Euler2D

/-- Signed area `½ ∫_0^{2π} Im(\bar z z') dθ` enclosed by a loop. -/
noncomputable def loopArea (z : ℝ → ℂ) : ℝ :=
  (1 / 2) * ∫ θ in (0 : ℝ)..2 * π, (conj (z θ) * deriv z θ).im

/-- The reference circle `z⁰(θ) = d e^{iθ}`. -/
noncomputable def refCircle (d : ℝ) (θ : ℝ) : ℂ := d * exp (θ * I)

/-- The linear functional `ℓ(v) = d ∫_0^{2π} Re(e^{-iθ} v(θ)) dθ`. -/
noncomputable def ellFun (d : ℝ) (v : ℝ → ℂ) : ℝ :=
  d * ∫ θ in (0 : ℝ)..2 * π, (exp (-(θ * I)) * v θ).re

/-- The area-correction coefficient `c(v) = √(1 − 𝒜(v)/(πd²)) − 1`. -/
noncomputable def chartCoeff (d : ℝ) (v : ℝ → ℂ) : ℝ :=
  Real.sqrt (1 - loopArea v / (π * d ^ 2)) - 1

/-- The fixed-area chart `Ξ(v) = (1 + c(v)) z⁰ + v`. -/
noncomputable def areaChart (d : ℝ) (v : ℝ → ℂ) : ℝ → ℂ :=
  fun θ => ((1 + chartCoeff d v : ℝ) : ℂ) * refCircle d θ + v θ

/-- The rotation/reparametrization `(G_ϑ z)(θ) = e^{iϑ} z(θ − ϑ)`. -/
noncomputable def rotShift (ϑ : ℝ) (z : ℝ → ℂ) : ℝ → ℂ := fun θ => exp (ϑ * I) * z (θ - ϑ)

lemma hasDerivAt_refCircle (d θ : ℝ) :
    HasDerivAt (refCircle d) (d * (I * exp (θ * I))) θ := by
  have h : HasDerivAt (fun t : ℝ => (t : ℂ) * I) (1 * I) θ :=
    (hasDerivAt_id θ).ofReal_comp.mul_const I
  have := (h.cexp).const_mul (d : ℂ)
  unfold refCircle
  simpa only [one_mul, mul_one, mul_comm, mul_left_comm, mul_assoc] using this

lemma deriv_refCircle (d : ℝ) : deriv (refCircle d) = fun θ : ℝ => d * (I * exp (θ * I)) :=
  funext fun θ => (hasDerivAt_refCircle d θ).deriv

/-- Integration by parts for the cross term, using periodicity. -/
lemma cross_term_integral (d : ℝ) {v : ℝ → ℂ} (hv : ContDiff ℝ 1 v)
    (hper : Function.Periodic v (2 * π)) :
    ∫ θ in (0 : ℝ)..2 * π,
        ((conj (refCircle d θ) * deriv v θ).im + (conj (v θ) * deriv (refCircle d) θ).im) =
      2 * d * ∫ θ in (0 : ℝ)..2 * π, (exp (-(θ * I)) * v θ).re := by
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hvc : Continuous (deriv v) := hv.continuous_deriv le_rfl
  set E : ℝ → ℂ := fun θ => exp (-(θ * I)) with hE
  have hEd : ∀ θ : ℝ, HasDerivAt E (-I * E θ) θ := by
    intro θ
    have h : HasDerivAt (fun t : ℝ => -((t : ℂ) * I)) (-(1 * I)) θ :=
      ((hasDerivAt_id θ).ofReal_comp.mul_const I).neg
    convert h.cexp using 1
    simp [hE]; ring
  have hEc : Continuous E := by fun_prop
  set w : ℝ → ℂ := fun θ => (d : ℂ) * E θ * v θ with hw
  set w' : ℝ → ℂ := fun θ => (d : ℂ) * (-I * E θ) * v θ + (d : ℂ) * E θ * deriv v θ with hw'
  have hwd : ∀ θ, HasDerivAt w (w' θ) θ := by
    intro θ
    exact ((hEd θ).const_mul (d : ℂ)).mul (hvd θ).hasDerivAt
  have hwi : ∀ θ, HasDerivAt (fun t => (w t).im) ((w' θ).im) θ := fun θ =>
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ (hwd θ)
  have hvc0 : Continuous v := hv.continuous
  have hw'c : Continuous w' := by
    simp only [hw']; fun_prop
  have hper_w : (w (2 * π)).im = (w 0).im := by
    have h1 : E (2 * π) = E 0 := by
      simp only [hE]
      rw [show -(((2 * π : ℝ) : ℂ) * I) = -(2 * π * I) by push_cast; ring, Complex.exp_neg,
        Complex.exp_two_pi_mul_I]
      simp
    simp only [hw, h1, show v (2 * π) = v 0 by simpa using hper 0]
  have hFTC : ∫ θ in (0 : ℝ)..2 * π, (w' θ).im = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hwi θ)
      ((Complex.continuous_im.comp hw'c).intervalIntegrable _ _), hper_w, sub_self]
  have hpt : ∀ θ : ℝ, (conj (refCircle d θ) * deriv v θ).im +
      (conj (v θ) * deriv (refCircle d) θ).im = (w' θ).im + 2 * d * (E θ * v θ).re := by
    intro θ
    have hconj : conj (refCircle d θ) = d * E θ := by
      simp only [refCircle, hE, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
      congr 2
      simp
    have hEconj : exp (θ * I) = conj (E θ) := by
      simp only [hE, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring_nf
    rw [hconj, deriv_refCircle]
    simp only
    rw [hEconj]
    simp only [hw', Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_add,
    hFTC, intervalIntegral.integral_const_mul]
  · ring
  · exact (Complex.continuous_im.comp hw'c).intervalIntegrable _ _
  · exact (continuous_const.mul (Complex.continuous_re.comp (hEc.mul hv.continuous))).intervalIntegrable _ _

/-- The quadratic identity `𝒜(b z⁰ + v) = b² π d² + b ℓ(v) + 𝒜(v)`. -/
theorem loopArea_affine (d b : ℝ) {v : ℝ → ℂ} (hv : ContDiff ℝ 1 v)
    (hper : Function.Periodic v (2 * π)) :
    loopArea (fun θ => (b : ℂ) * refCircle d θ + v θ) =
      b ^ 2 * (π * d ^ 2) + b * ellFun d v + loopArea v := by
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hvc : Continuous (deriv v) := hv.continuous_deriv le_rfl
  have hvc0 : Continuous v := hv.continuous
  have hder : deriv (fun θ => (b : ℂ) * refCircle d θ + v θ) =
      fun θ => (b : ℂ) * deriv (refCircle d) θ + deriv v θ := by
    funext θ
    exact (((hasDerivAt_refCircle d θ).const_mul (b : ℂ)).add (hvd θ).hasDerivAt).deriv.trans
      (by rw [deriv_refCircle])
  have hz0 : ∀ θ : ℝ, (conj (refCircle d θ) * deriv (refCircle d) θ).im = d ^ 2 := by
    intro θ
    rw [deriv_refCircle]
    simp only [refCircle, map_mul, Complex.conj_ofReal]
    have he : conj (exp (θ * I)) * exp (θ * I) = 1 := by
      rw [Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]; simp
    have h2 : (d : ℂ) * conj (exp (θ * I)) * (d * (I * exp (θ * I))) =
        (d ^ 2 : ℝ) * I * (conj (exp (θ * I)) * exp (θ * I)) := by
      push_cast; ring
    rw [h2, he]; simp only [mul_one, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have hpt : ∀ θ : ℝ, (conj ((b : ℂ) * refCircle d θ + v θ) *
      ((b : ℂ) * deriv (refCircle d) θ + deriv v θ)).im =
      b ^ 2 * d ^ 2 + b * ((conj (refCircle d θ) * deriv v θ).im +
        (conj (v θ) * deriv (refCircle d) θ).im) + (conj (v θ) * deriv v θ).im := by
    intro θ
    rw [← hz0 θ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.add_im, Complex.mul_im,
      Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hc1 : Continuous (deriv (refCircle d)) := by rw [deriv_refCircle]; fun_prop
  have hc2 : Continuous (refCircle d) := by unfold refCircle; fun_prop
  have hi1 : IntervalIntegrable (fun θ => (conj (refCircle d θ) * deriv v θ).im +
      (conj (v θ) * deriv (refCircle d) θ).im) volume 0 (2 * π) :=
    (Continuous.add (Complex.continuous_im.comp ((Complex.continuous_conj.comp hc2).mul hvc))
      (Complex.continuous_im.comp ((Complex.continuous_conj.comp hvc0).mul hc1))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ => (conj (v θ) * deriv v θ).im) volume 0 (2 * π) :=
    (Complex.continuous_im.comp ((Complex.continuous_conj.comp hvc0).mul hvc)).intervalIntegrable _ _
  unfold loopArea
  rw [hder, intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    cross_term_integral d hv hper]
  · simp only [ellFun, smul_eq_mul]; ring
  · exact _root_.intervalIntegrable_const
  · exact hi1.const_mul b
  · exact (_root_.intervalIntegrable_const).add (hi1.const_mul b)
  · exact hi2

/-- The chart takes values in the loops of area `π d²`. -/
theorem loopArea_areaChart {d : ℝ} (hd : d ≠ 0) {v : ℝ → ℂ} (hv : ContDiff ℝ 1 v)
    (hper : Function.Periodic v (2 * π)) (hℓ : ellFun d v = 0)
    (hA : loopArea v ≤ π * d ^ 2) :
    loopArea (areaChart d v) = π * d ^ 2 := by
  have hpd : 0 < π * d ^ 2 := by positivity
  have hs : 0 ≤ 1 - loopArea v / (π * d ^ 2) := by
    rw [sub_nonneg, div_le_one hpd]; exact hA
  have h := loopArea_affine d (1 + chartCoeff d v) hv hper
  rw [hℓ] at h
  rw [show areaChart d v = fun θ => ((1 + chartCoeff d v : ℝ) : ℂ) * refCircle d θ + v θ from rfl,
    h, show 1 + chartCoeff d v = Real.sqrt (1 - loopArea v / (π * d ^ 2)) by
      simp [chartCoeff], Real.sq_sqrt hs]
  field_simp
  ring

/-- Uniqueness of the area coefficient: a loop `(1 + t) z⁰ + v` with `ℓ(v) = 0`, `1 + t > 0`
and area `π d²` is `Ξ(v)`. -/
theorem chart_coeff_unique {d : ℝ} (hd : d ≠ 0) {v : ℝ → ℂ} (hv : ContDiff ℝ 1 v)
    (hper : Function.Periodic v (2 * π)) (hℓ : ellFun d v = 0) {t : ℝ} (ht : 0 < 1 + t)
    (hA : loopArea (fun θ => ((1 + t : ℝ) : ℂ) * refCircle d θ + v θ) = π * d ^ 2) :
    t = chartCoeff d v := by
  have hpd : 0 < π * d ^ 2 := by positivity
  rw [loopArea_affine d (1 + t) hv hper, hℓ] at hA
  have h1 : (1 + t) ^ 2 = 1 - loopArea v / (π * d ^ 2) := by
    field_simp; linarith
  have h2 : 1 + t = Real.sqrt (1 - loopArea v / (π * d ^ 2)) := by
    rw [← h1, Real.sqrt_sq ht.le]
  unfold chartCoeff; linarith

/-- `ℓ(z⁰) = 2π d²`. -/
lemma ellFun_refCircle (d : ℝ) : ellFun d (refCircle d) = 2 * π * d ^ 2 := by
  have : ∀ θ : ℝ, (exp (-(θ * I)) * refCircle d θ).re = d := by
    intro θ
    simp only [refCircle]
    rw [mul_left_comm, ← Complex.exp_add]
    simp
  simp only [ellFun, this, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Every loop decomposes as `z = (1 + t) z⁰ + v` with `t = ℓ(z − z⁰)/(2π d²)` and `ℓ(v) = 0`. -/
lemma ellFun_sub_mul (d : ℝ) {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    ellFun d (fun θ => f θ - (c : ℂ) * g θ) = ellFun d f - c * ellFun d g := by
  have hE : Continuous fun θ : ℝ => exp (-(θ * I)) := by fun_prop
  have hpt : ∀ θ : ℝ, (exp (-(θ * I)) * (f θ - (c : ℂ) * g θ)).re =
      (exp (-(θ * I)) * f θ).re - c * (exp (-(θ * I)) * g θ).re := by
    intro θ
    simp only [mul_sub, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  unfold ellFun
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ), intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul]
  · ring
  · exact (Complex.continuous_re.comp (hE.mul hf)).intervalIntegrable _ _
  · exact (continuous_const.mul (Complex.continuous_re.comp (hE.mul hg))).intervalIntegrable _ _

theorem chart_decomposition {d : ℝ} (hd : d ≠ 0) {z : ℝ → ℂ} (hz : Continuous z) :
    ∃ v : ℝ → ℂ, ellFun d v = 0 ∧
      z = fun θ => ((1 + ellFun d (fun θ => z θ - refCircle d θ) / (2 * π * d ^ 2) : ℝ) : ℂ) *
        refCircle d θ + v θ := by
  have hc : Continuous (refCircle d) := by unfold refCircle; fun_prop
  set t : ℝ := ellFun d (fun θ => z θ - refCircle d θ) / (2 * π * d ^ 2) with ht
  refine ⟨fun θ => z θ - ((1 + t : ℝ) : ℂ) * refCircle d θ, ?_, ?_⟩
  · have h1 := ellFun_sub_mul d hz hc 1
    have h2 := ellFun_sub_mul d hz hc (1 + t)
    simp only [Complex.ofReal_one, one_mul] at h1
    rw [h2, ellFun_refCircle]
    rw [ellFun_refCircle] at h1
    rw [ht, h1]
    field_simp
    ring
  · funext θ; ring

/-- Integrals over a period are invariant under translation. -/
lemma integral_period_comp_sub {f : ℝ → ℝ} (hf : Function.Periodic f (2 * π)) (ϑ : ℝ) :
    ∫ θ in (0 : ℝ)..2 * π, f (θ - ϑ) = ∫ θ in (0 : ℝ)..2 * π, f θ := by
  rw [intervalIntegral.integral_comp_sub_right]
  have := hf.intervalIntegral_add_eq (0 - ϑ) 0
  rw [show (0 : ℝ) - ϑ + 2 * π = 2 * π - ϑ by ring, zero_add] at this
  exact this

lemma periodic_deriv {v : ℝ → ℂ} {T : ℝ} (h : Function.Periodic v T) :
    Function.Periodic (deriv v) T := by
  intro x
  have : v = fun y => v (y + T) := funext fun y => (h y).symm
  conv_rhs => rw [this]
  rw [deriv_comp_add_const]

/-- `ℓ` is invariant under `G_ϑ`. -/
lemma ellFun_rotShift (d ϑ : ℝ) {v : ℝ → ℂ}
    (hper : Function.Periodic v (2 * π)) : ellFun d (rotShift ϑ v) = ellFun d v := by
  have hpt : ∀ θ : ℝ, (exp (-(θ * I)) * rotShift ϑ v θ).re =
      (exp (-(((θ - ϑ : ℝ) : ℂ) * I)) * v (θ - ϑ)).re := by
    intro θ
    simp only [rotShift, ← mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast; ring
  unfold ellFun
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  congr 1
  exact integral_period_comp_sub (f := fun θ => (exp (-((θ : ℂ) * I)) * v θ).re)
    (fun θ => by
      simp only
      rw [hper θ]
      congr 2
      rw [show -(((θ + 2 * π : ℝ) : ℂ) * I) = -((θ : ℂ) * I) + -(2 * π * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_neg (2 * π * I), Complex.exp_two_pi_mul_I]
      simp) ϑ

/-- `𝒜` is invariant under `G_ϑ`. -/
lemma loopArea_rotShift (ϑ : ℝ) {v : ℝ → ℂ} (hv : ContDiff ℝ 1 v)
    (hper : Function.Periodic v (2 * π)) : loopArea (rotShift ϑ v) = loopArea v := by
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hder : ∀ θ, deriv (rotShift ϑ v) θ = exp (ϑ * I) * deriv v (θ - ϑ) := by
    intro θ
    have h1 : HasDerivAt (fun x => v (x - ϑ)) (deriv v (θ - ϑ)) θ := by
      exact (hvd (θ - ϑ)).hasDerivAt.comp_sub_const θ ϑ
    exact (h1.const_mul (exp (ϑ * I))).deriv
  have he : conj (exp (ϑ * I)) * exp (ϑ * I) = 1 := by
    rw [Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]; simp
  have hpt : ∀ θ : ℝ, (conj (rotShift ϑ v θ) * deriv (rotShift ϑ v) θ).im =
      (conj (v (θ - ϑ)) * deriv v (θ - ϑ)).im := by
    intro θ
    rw [hder]
    simp only [rotShift, map_mul]
    rw [show conj (exp (ϑ * I)) * conj (v (θ - ϑ)) * (exp (ϑ * I) * deriv v (θ - ϑ)) =
      (conj (exp (ϑ * I)) * exp (ϑ * I)) * (conj (v (θ - ϑ)) * deriv v (θ - ϑ)) by ring, he,
      one_mul]
  unfold loopArea
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  congr 1
  exact integral_period_comp_sub (f := fun θ => (conj (v θ) * deriv v θ).im)
    (fun θ => by simp only; rw [hper θ, periodic_deriv hper θ]) ϑ

/-- `G_ϑ z⁰ = z⁰`. -/
lemma rotShift_refCircle (d ϑ : ℝ) : rotShift ϑ (refCircle d) = refCircle d := by
  funext θ
  simp only [rotShift, refCircle]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast; ring

/-- Equivariance of the area chart: `Ξ(G_ϑ v) = G_ϑ Ξ(v)`. -/
theorem areaChart_equivariant (d ϑ : ℝ) {v : ℝ → ℂ} (hv : ContDiff ℝ 1 v)
    (hper : Function.Periodic v (2 * π)) :
    areaChart d (rotShift ϑ v) = rotShift ϑ (areaChart d v) := by
  have hc : chartCoeff d (rotShift ϑ v) = chartCoeff d v := by
    simp only [chartCoeff, loopArea_rotShift ϑ hv hper]
  funext θ
  have h0 := congrFun (rotShift_refCircle d ϑ) θ
  simp only [rotShift] at h0
  simp only [areaChart, rotShift, hc]
  rw [mul_add, ← h0]
  ring

end Euler2D
