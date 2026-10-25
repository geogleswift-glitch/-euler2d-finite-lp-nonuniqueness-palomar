module

public import Mathlib

/-!
# The diagonal rotating equation (Lemma `ib:lem:diagonal-frame`)

A two-interface contour is a pair `z = (z₁, z₂)` in `E × E`, where `E` is any complex normed
space of contours (the value rotation `z ↦ e^{iφ} z` is scalar multiplication). Put
`S(τ)(z₁, z₂) = (e^{iτ/2} z₁, z₂)` (`rotS`), `Q(w₁, w₂) = (i w₁/2, 0)` (`genQ`) and
`G(τ, w) = S(−τ) F(S(τ) w) − Q w` (`diagG`).

For a contour vector field `F` that is covariant under value rotations,
`F(c z) = c F(z)` for `|c| = 1`, we prove:

* `diagonal_rotating_equation`: if `ż = A F(z) + iβ z`, then `w(t) = e^{-iβt} S(−At) z(t)`
  solves `ẇ = A G(At, w)`; equivalently `z = e^{iβt} S(At) w` (`rotating_substitution`).
* `diagG_periodic`: `G(τ + 4π, w) = G(τ, w)`.
* `diagG_circular`: if `S(τ) z⁰` is a material solution of `ż = F(z)` then `G(τ, z⁰) = 0`.

The uniform local derivative bounds for `G` are not formalized.
-/

@[expose] public section

open Complex Real

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `S(τ)(z₁, z₂) = (e^{iτ/2} z₁, z₂)`. -/
noncomputable def rotS (τ : ℝ) (z : E × E) : E × E := (exp ((τ / 2 : ℝ) * I) • z.1, z.2)

/-- The generator `Q(w₁, w₂) = (i w₁ / 2, 0)` of `S`. -/
noncomputable def genQ (w : E × E) : E × E := ((I / 2) • w.1, 0)

/-- The rotating-frame vector field `G(τ, w) = S(−τ) F(S(τ) w) − Q w`. -/
noncomputable def diagG (F : E × E → E × E) (τ : ℝ) (w : E × E) : E × E :=
  rotS (-τ) (F (rotS τ w)) - genQ w

/-- Covariance of a contour vector field under value rotations. -/
def RotCovariant (F : E × E → E × E) : Prop := ∀ c : ℂ, ‖c‖ = 1 → ∀ z, F (c • z) = c • F z

lemma rotS_add (a b : ℝ) (z : E × E) : rotS a (rotS b z) = rotS (a + b) z := by
  simp only [rotS, smul_smul, ← Complex.exp_add]
  congr 3
  push_cast; ring

lemma rotS_zero (z : E × E) : rotS 0 z = z := by
  simp [rotS]

lemma rotS_neg_rotS (τ : ℝ) (z : E × E) : rotS (-τ) (rotS τ z) = z := by
  rw [rotS_add, neg_add_cancel, rotS_zero]

lemma rotS_smul (τ : ℝ) (c : ℂ) (z : E × E) : rotS τ (c • z) = c • rotS τ z := by
  simp only [rotS, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]
  rw [smul_comm]

/-- The substitution `z = e^{iβt} S(At) w` is inverted by `w = e^{-iβt} S(−At) z`. -/
lemma rotating_substitution (A β t : ℝ) (z : E × E) :
    exp ((β * t : ℝ) * I) • rotS (A * t) (exp (-((β * t : ℝ) * I)) • rotS (-(A * t)) z) = z := by
  rw [rotS_smul, rotS_add, add_neg_cancel, rotS_zero, smul_smul, ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero, one_smul]

/-- **Lemma `ib:lem:diagonal-frame`.** If `ż = A F(z) + iβ z`, then
`w(t) = e^{-iβt} S(−At) z(t)` satisfies `ẇ = A G(At, w)`. -/
theorem diagonal_rotating_equation {F : E × E → E × E} (hF : RotCovariant F) (A β : ℝ)
    {z : ℝ → E × E}
    (hz : ∀ t, HasDerivAt z ((A : ℂ) • F (z t) + ((β : ℂ) * I) • z t) t) (t : ℝ) :
    HasDerivAt (fun s => exp (-((β * s : ℝ) * I)) • rotS (-(A * s)) (z s))
      ((A : ℂ) • diagG F (A * t) (exp (-((β * t : ℝ) * I)) • rotS (-(A * t)) (z t))) t := by
  set e2 : ℝ → ℂ := fun s => exp (-((β * s : ℝ) * I)) with he2
  set e3 : ℝ → ℂ := fun s => exp (((-(A * s)) / 2 : ℝ) * I) with he3
  have hfun : (fun s => exp (-((β * s : ℝ) * I)) • rotS (-(A * s)) (z s)) =
      fun s => ((e2 s * e3 s) • (z s).1, e2 s • (z s).2) := by
    funext s
    simp only [rotS, Prod.smul_mk, smul_smul, he2, he3]
  have hd2 : HasDerivAt e2 (e2 t * (-((β : ℂ) * I))) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(((β * s : ℝ) : ℂ) * I)) (-((((β * 1 : ℝ)) : ℂ) * I)) t :=
      ((((hasDerivAt_id t).const_mul β).ofReal_comp).mul_const I).neg
    convert h1.cexp using 1
    simp only [he2]; push_cast; ring_nf
  have hd3 : HasDerivAt e3 (e3 t * (-((A : ℂ) / 2 * I))) t := by
    have h1 : HasDerivAt (fun s : ℝ => (((-(A * s)) / 2 : ℝ) : ℂ) * I)
        (((((-(A * 1)) / 2 : ℝ)) : ℂ) * I) t :=
      (((((hasDerivAt_id t).const_mul A).neg.div_const 2).ofReal_comp).mul_const I)
    convert h1.cexp using 1
    simp only [he3]; push_cast; ring_nf
  rw [hfun]
  have hz1 := (hz t).fst
  have hz2 := (hz t).snd
  have hD := ((hd2.mul hd3).smul hz1).prodMk (hd2.smul hz2)
  convert hD using 1
  -- identify `F` at the rotated point using covariance
  have hnorm : ‖e2 t‖ = 1 := by
    simp only [he2]
    rw [show -(((β * t : ℝ) : ℂ) * I) = ((-(β * t) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hrot : rotS (A * t) (e2 t • rotS (-(A * t)) (z t)) = e2 t • z t := by
    rw [rotS_smul, rotS_add, add_neg_cancel, rotS_zero]
  simp only [diagG]
  rw [show exp (-((β * t : ℝ) * I)) = e2 t from rfl, hrot, hF _ hnorm]
  simp only [rotS, genQ, he3, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, Prod.fst_add,
    Prod.snd_add, Prod.mk_sub_mk, smul_add, smul_sub, sub_zero]
  ext
  · simp only [smul_smul]
    simp only [Pi.mul_apply]
    module
  · simp only [smul_smul]
    module

/-- `G` is `4π`-periodic in `τ`. -/
theorem diagG_periodic (F : E × E → E × E) (τ : ℝ) (w : E × E) :
    diagG F (τ + 4 * π) w = diagG F τ w := by
  have h : ∀ a : ℝ, rotS (a + 4 * π) = (rotS a : E × E → E × E) := by
    intro a
    funext z
    simp only [rotS]
    congr 2
    rw [show (((a + 4 * π) / 2 : ℝ) : ℂ) * I = ((a / 2 : ℝ) : ℂ) * I + 2 * π * I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h2 : rotS (-(τ + 4 * π)) = (rotS (-τ) : E × E → E × E) := by
    rw [← h (-(τ + 4 * π)), show -(τ + 4 * π) + 4 * π = -τ by ring]
  simp only [diagG, h, h2]

/-- The circular reference is an equilibrium of the rotating-frame equation: if `τ ↦ S(τ) z⁰`
solves `ż = F(z)`, then `G(τ, z⁰) = 0`. -/
theorem diagG_circular (F : E × E → E × E) (z0 : E × E)
    (hcirc : ∀ τ, HasDerivAt (fun s => rotS s z0) (F (rotS τ z0)) τ) (τ : ℝ) :
    diagG F τ z0 = 0 := by
  have hd : HasDerivAt (fun s : ℝ => rotS s z0) (genQ (rotS τ z0)) τ := by
    have h1 : HasDerivAt (fun s : ℝ => ((s / 2 : ℝ) : ℂ) * I) ((((1 : ℝ) / 2 : ℝ) : ℂ) * I) τ :=
      (((hasDerivAt_id τ).div_const 2).ofReal_comp).mul_const I
    have h2 := (h1.cexp).smul_const z0.1
    have h3 := h2.prodMk (hasDerivAt_const τ z0.2)
    convert h3 using 1 <;> simp only [genQ, rotS, smul_smul]
    congr 1
    · congr 1; push_cast; ring
  have := (hcirc τ).unique hd
  rw [diagG, this]
  simp only [genQ, rotS]
  ext
  · simp only [Prod.fst_sub, smul_smul, Prod.fst_zero]
    have hexp : exp (((-τ / 2 : ℝ)) * I) * exp (((τ / 2 : ℝ)) * I) = 1 := by
      rw [← Complex.exp_add, show (((-τ / 2 : ℝ)) : ℂ) * I + ((τ / 2 : ℝ) : ℂ) * I = 0 by
        push_cast; ring, Complex.exp_zero]
    rw [show exp (((-τ / 2 : ℝ)) * I) * (I / 2 * exp (((τ / 2 : ℝ)) * I)) =
      I / 2 * (exp (((-τ / 2 : ℝ)) * I) * exp (((τ / 2 : ℝ)) * I)) by ring, hexp, mul_one,
      sub_self]
  · simp

end Euler2D
