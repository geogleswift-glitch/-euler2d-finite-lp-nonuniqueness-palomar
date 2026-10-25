module

public import Mathlib

/-!
# Transported labels (Corollary `bv:labels`, flow-theoretic part)

Let `X t : ℂ → ℂ` be the particle flow at time `t` (from time `0`), with inverse `Y t`, both
jointly continuous in `(t, a)`, and each `X t` measure preserving. For a label `D` put
`D(t) = X t '' D`.

* `label_image_eq_preimage`, `label_indicator`: `1_{D(t)} = 1_D ∘ Y t`.
* `label_area`: `|D(t)| = |D|` for measurable `D`.
* `label_combination`: finite linear combinations of labels are transported.
* `label_subset`: inclusions are preserved.
* `boundary_separation`: initially disjoint compact sets stay a uniform positive distance apart
  on every `[0, T]`.
* `label_rot_invariant`: if the flow commutes with the quarter turn, quarter-turn invariant
  labels stay invariant.
* `origin_separation`, `origin_disk`: if the origin is fixed, a compact set avoiding it stays a
  uniform positive distance away, and an open label containing it contains one fixed disk
  about it on `[0, T]`.

That the Euler particle flow has these properties is the content of Theorem `bv:wellposed`,
which is not formalized here; the weak transport equation for labels is not formalized.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace Euler2D

variable {X Y : ℝ → ℂ → ℂ}

lemma label_image_eq_preimage (hXY : ∀ t a, Y t (X t a) = a) (hYX : ∀ t z, X t (Y t z) = z)
    (t : ℝ) (D : Set ℂ) : X t '' D = Y t ⁻¹' D := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mem_preimage, hXY] using ha
  · intro hz
    exact ⟨Y t z, hz, hYX t z⟩

/-- `1_{D(t)} = 1_D ∘ Y t`. -/
theorem label_indicator (hXY : ∀ t a, Y t (X t a) = a) (hYX : ∀ t z, X t (Y t z) = z)
    (t : ℝ) (D : Set ℂ) (z : ℂ) :
    (X t '' D).indicator (1 : ℂ → ℝ) z = D.indicator 1 (Y t z) := by
  rw [label_image_eq_preimage hXY hYX]
  rfl

/-- Area preservation: `|D(t)| = |D|`. -/
theorem label_area (hXY : ∀ t a, Y t (X t a) = a) (hYX : ∀ t z, X t (Y t z) = z)
    (hYc : Continuous fun p : ℝ × ℂ => Y p.1 p.2) (hmp : ∀ t, MeasurePreserving (X t))
    (t : ℝ) {D : Set ℂ} (hD : MeasurableSet D) : volume (X t '' D) = volume D := by
  have hYt : Continuous (Y t) := hYc.comp (continuous_const.prodMk continuous_id)
  rw [label_image_eq_preimage hXY hYX]
  have hS : MeasurableSet (Y t ⁻¹' D) := hYt.measurable hD
  have hpre : X t ⁻¹' (Y t ⁻¹' D) = D := by
    ext a; simp [hXY]
  rw [← (hmp t).measure_preimage hS.nullMeasurableSet, hpre]

/-- Finite linear combinations of labels are transported. -/
theorem label_combination (hXY : ∀ t a, Y t (X t a) = a) (hYX : ∀ t z, X t (Y t z) = z)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (D : ι → Set ℂ) (t : ℝ) (z : ℂ) :
    ∑ j ∈ s, c j * (X t '' D j).indicator 1 z = ∑ j ∈ s, c j * (D j).indicator 1 (Y t z) := by
  simp_rw [label_indicator hXY hYX]

/-- Inclusions are preserved. -/
theorem label_subset (t : ℝ) {D E : Set ℂ} (h : D ⊆ E) : X t '' D ⊆ X t '' E :=
  image_mono h

/-- Initially disjoint compact sets stay a uniform positive distance apart on `[0, T]`. -/
theorem boundary_separation (hXY : ∀ t a, Y t (X t a) = a)
    (hXc : Continuous fun p : ℝ × ℂ => X p.1 p.2) {Γ₁ Γ₂ : Set ℂ} (h₁ : IsCompact Γ₁)
    (h₂ : IsCompact Γ₂) (hdisj : Disjoint Γ₁ Γ₂) (T : ℝ) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, δ ≤ dist (X t a) (X t b) := by
  set K := Icc 0 T ×ˢ Γ₁ ×ˢ Γ₂ with hK
  have hKc : IsCompact K := isCompact_Icc.prod (h₁.prod h₂)
  set F : ℝ × ℂ × ℂ → ℝ := fun p => dist (X p.1 p.2.1) (X p.1 p.2.2) with hF
  have hFc : Continuous F :=
    (hXc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).dist
      (hXc.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  rcases K.eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun t ht a ha b hb => ?_⟩
    have : (t, a, b) ∈ K := ⟨ht, ha, hb⟩
    rw [hemp] at this
    exact absurd this (notMem_empty _)
  obtain ⟨p, hp, hmin⟩ := hKc.exists_isMinOn hne hFc.continuousOn
  refine ⟨F p, ?_, fun t ht a ha b hb => hmin (show (t, a, b) ∈ K from ⟨ht, ha, hb⟩)⟩
  have hab : p.2.1 ≠ p.2.2 := fun h => Set.disjoint_left.mp hdisj hp.2.1 (h ▸ hp.2.2)
  have hX : X p.1 p.2.1 ≠ X p.1 p.2.2 := fun h => hab (by
    have := congrArg (Y p.1) h; rwa [hXY, hXY] at this)
  exact dist_pos.mpr hX

/-- Quarter-turn invariant labels remain invariant under a quarter-turn equivariant flow. -/
theorem label_rot_invariant (hrot : ∀ t a, X t (Complex.I * a) = Complex.I * X t a) (t : ℝ)
    {D : Set ℂ} (hD : ∀ a, Complex.I * a ∈ D ↔ a ∈ D) (z : ℂ) :
    Complex.I * z ∈ X t '' D ↔ z ∈ X t '' D := by
  have hrot' : ∀ a, X t (-Complex.I * a) = -Complex.I * X t a := by
    intro a
    have h := hrot t (-Complex.I * a)
    have e : Complex.I * (-Complex.I * a) = a := by ring_nf; simp [Complex.I_sq]
    rw [e] at h
    rw [h]; ring_nf; simp [Complex.I_sq]
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨-Complex.I * a, ?_, ?_⟩
    · apply (hD _).mp
      have e : Complex.I * (-Complex.I * a) = a := by ring_nf; simp [Complex.I_sq]
      rwa [e]
    · rw [hrot', h]; ring_nf; simp [Complex.I_sq]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Complex.I * a, (hD a).mpr ha, hrot t a⟩

/-- A compact set avoiding the fixed origin stays a uniform positive distance from it. -/
theorem origin_separation (hXY : ∀ t a, Y t (X t a) = a)
    (hXc : Continuous fun p : ℝ × ℂ => X p.1 p.2) (h0 : ∀ t, X t 0 = 0) {Γ : Set ℂ}
    (hΓ : IsCompact Γ) (hΓ0 : (0 : ℂ) ∉ Γ) (T : ℝ) :
    ∃ δ > 0, ∀ t ∈ Icc 0 T, ∀ a ∈ Γ, δ ≤ ‖X t a‖ := by
  obtain ⟨δ, hδ, h⟩ := boundary_separation hXY hXc hΓ isCompact_singleton
    (Set.disjoint_singleton_right.mpr hΓ0) T
  refine ⟨δ, hδ, fun t ht a ha => ?_⟩
  have := h t ht a ha 0 rfl
  rwa [h0, dist_zero_right] at this

/-- An open label containing the fixed origin contains one fixed disk about it on `[0, T]`. -/
theorem origin_disk (hYX : ∀ t z, X t (Y t z) = z)
    (hYc : Continuous fun p : ℝ × ℂ => Y p.1 p.2) (h0 : ∀ t, Y t 0 = 0) {D : Set ℂ}
    (hD : IsOpen D) (hD0 : (0 : ℂ) ∈ D) (T : ℝ) :
    ∃ r > 0, ∀ t ∈ Icc 0 T, ball 0 r ⊆ X t '' D := by
  set N := {p : ℝ × ℂ | Y p.1 p.2 ∈ D} with hN
  have hNo : IsOpen N := hD.preimage hYc
  have hsub : Icc 0 T ×ˢ ({0} : Set ℂ) ⊆ N := by
    rintro ⟨t, z⟩ ⟨_, hz⟩
    have hz' : z = 0 := hz
    show Y t z ∈ D
    rw [hz', h0]; exact hD0
  obtain ⟨u, v, _, hv, hsu, hsv, huv⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hNo hsub
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hv 0 (hsv rfl)
  refine ⟨r, hr, fun t ht z hz => ?_⟩
  have : (t, z) ∈ N := huv ⟨hsu ht, hball hz⟩
  exact ⟨Y t z, this, hYX t z⟩

end Euler2D
