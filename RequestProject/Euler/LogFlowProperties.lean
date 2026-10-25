module

public import RequestProject.Euler.LogFlowGlobal

/-!
# Injectivity and symmetry of logarithmic-modulus particle flows

Backward comparison proves injectivity, while forward uniqueness retains
the fixed origin and spatial translation symmetries of the actual field.
-/

@[expose] public section

noncomputable section

open Set Filter Topology Real

namespace Euler2D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem logFlow_origin_fixed {T C : ℝ} (hC : 0 ≤ C)
    {v : ℝ → E → E} {X : ℝ → E}
    (hXc : Continuous X) (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (v t (X t)) t)
    (hinit : X 0 = 0) (hzero : ∀ t ∈ Icc 0 T, v t 0 = 0)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∀ t ∈ Icc 0 T, X t = 0 := by
  apply logFlow_unique hC hXc continuous_const hX _ hinit hlip
  intro t ht
  rw [hzero t ht]
  exact hasDerivAt_const t (0 : E)

theorem logFlow_translation_equivariant {T C : ℝ} (hC : 0 ≤ C)
    {v X : ℝ → E → E} (c : E)
    (hXc : Continuous (Function.uncurry X))
    (hX : ∀ a t, t ∈ Icc 0 T → HasDerivAt (fun s => X s a) (v t (X t a)) t)
    (hinit : ∀ a, X 0 a = a)
    (hperiod : ∀ t ∈ Icc 0 T, ∀ x, v t (x + c) = v t x)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∀ a t, t ∈ Icc 0 T → X t (a + c) = X t a + c := by
  intro a
  apply logFlow_unique hC
    (hXc.comp (continuous_id.prodMk continuous_const))
    ((hXc.comp (continuous_id.prodMk continuous_const)).add continuous_const)
    (hX (a + c)) _ (by
      change X 0 (a + c) = X 0 a + c
      rw [hinit, hinit]) hlip
  intro t ht
  change HasDerivAt (fun s => X s a + c) (v t (X t a + c)) t
  rw [hperiod t ht]
  exact (hX a t ht).add_const c

/-- Coinciding particles cannot have distinct initial labels, even
though the vector field is only logarithmically continuous in space. -/
theorem logFlow_injective {T C : ℝ} (hC : 0 ≤ C)
    {v X : ℝ → E → E} (hXc : Continuous (Function.uncurry X))
    (hX : ∀ a t, t ∈ Icc 0 T → HasDerivAt (fun s => X s a) (v t (X t a)) t)
    (hinit : ∀ a, X 0 a = a)
    (hlip : ∀ t ∈ Icc 0 T, ∀ x y : E, ‖x - y‖ ≤ 1 / 2 →
      ‖v t x - v t y‖ ≤ C * logFlowModulus ‖x - y‖) :
    ∀ t ∈ Icc 0 T, Function.Injective (X t) := by
  intro t ht a b hab
  have htime (s : ℝ) (hs : s ∈ Icc 0 t) : t - s ∈ Icc 0 T := by
    exact ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
  have hrev (a : E) (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivAt (fun r => X (t - r) a) (-v (t - s) (X (t - s) a)) s := by
    simpa only [Function.comp_def, id_eq, zero_sub, neg_one_smul] using
      (hX a (t - s) (htime s hs)).scomp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
  have hcomp (a : E) : Continuous (fun s => X (t - s) a) :=
    hXc.comp ((continuous_const.sub continuous_id).prodMk continuous_const)
  have hsame := logFlow_unique hC (v := fun s x => -v (t - s) x)
    (hcomp a) (hcomp b) (hrev a) (hrev b) (by simpa only [sub_zero] using hab)
    (by
      intro s hs x y hxy
      simpa only [neg_sub_neg, norm_sub_rev] using hlip (t - s) (htime s hs) x y hxy)
  simpa only [sub_self, hinit] using hsame t ⟨ht.1, le_rfl⟩

end Euler2D

end
