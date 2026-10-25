module

public import RequestProject.Euler.TorusModel
public import RequestProject.Euler.LagrangianTransport

/-!
# Periodic transport and fundamental-domain representatives

A continuous particle trajectory on the covering plane can cross a face
of the square. Area preservation is therefore imposed on its measurable
representative in the square. Periodic tests agree on both representatives,
which connects that area preservation to the actual particle equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Euler2D

def torusWrap (x : R2) : R2 := torusRep (torusProj x)

lemma measurable_torusWrap : Measurable torusWrap :=
  measurable_torusRep.comp measurable_torusProj

lemma torusWrap_ae : torusWrap =ᵐ[μT] id := torusRep_torusProj_ae

lemma torusProj_periodic : IsTorusPeriodic torusProj := by
  intro x i
  funext j
  by_cases h : i = j
  · subst j
    simp only [torusProj, PiLp.add_apply, EuclideanSpace.single_apply, ↓reduceIte]
    rw [add_div, div_self (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    exact AddCircle.coe_add_period _ _
  · simp [torusProj, EuclideanSpace.single_apply, Ne.symm h]

lemma isTorusPeriodic_torusWrap : IsTorusPeriodic torusWrap :=
  fun x i => congrArg torusRep (torusProj_periodic x i)

lemma IsTorusPeriodic.eq_of_torusProj_eq {F : Type*} {f : R2 → F}
    (hf : IsTorusPeriodic f) {x y : R2} (h : torusProj x = torusProj y) : f x = f y := by
  have hcoord (i : Fin 2) : ∃ n : ℤ, y i = x i + (n : ℝ) * (2 * Real.pi) := by
    have heq := congrFun h i
    have hm : x i / (2 * Real.pi) ≡ y i / (2 * Real.pi) [PMOD (1 : ℝ)] :=
      AddCommGroup.modEq_iff_eq_mod_zmultiples.mpr heq
    obtain ⟨n, hn⟩ := AddCommGroup.modEq_iff_eq_add_zsmul.mp hm
    refine ⟨n, ?_⟩
    have hP : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    simp only [zsmul_eq_mul, mul_one] at hn
    field_simp [hP] at hn
    linarith
  obtain ⟨n₀, hn₀⟩ := hcoord 0
  obtain ⟨n₁, hn₁⟩ := hcoord 1
  have hy : y = (x + n₀ • EuclideanSpace.single 0 (2 * Real.pi)) +
      n₁ • EuclideanSpace.single 1 (2 * Real.pi) := by
    ext i
    fin_cases i <;> simpa [EuclideanSpace.single_apply, zsmul_eq_mul] using (by assumption)
  have hp (i : Fin 2) : Function.Periodic f (EuclideanSpace.single i (2 * Real.pi)) :=
    fun x => hf x i
  rw [hy, (hp 1).zsmul n₁, (hp 0).zsmul n₀]

lemma IsTorusPeriodic.eq_torusWrap {F : Type*} {f : R2 → F}
    (hf : IsTorusPeriodic f) (x : R2) : f (torusWrap x) = f x :=
  hf.eq_of_torusProj_eq (torusProj_torusRep (torusProj x))

/-- Periodic extension of any fundamental-domain function. -/
def torusExtension {F : Type*} (f : R2 → F) : R2 → F := f ∘ torusWrap

lemma isTorusPeriodic_torusExtension {F : Type*} (f : R2 → F) :
    IsTorusPeriodic (torusExtension f) :=
  fun x i => congrArg f (isTorusPeriodic_torusWrap x i)

lemma torusExtension_ae {F : Type*} (f : R2 → F) : torusExtension f =ᵐ[μT] f := by
  filter_upwards [torusWrap_ae] with x hx
  simp only [torusExtension, Function.comp_apply, hx, id_eq]

def TorusAreaPreserving (X : R2 → R2) : Prop :=
  MeasurePreserving (torusWrap ∘ X) μT μT

lemma TorusAreaPreserving.eLpNorm_comp {X : R2 → R2} (hX : TorusAreaPreserving X)
    {F : Type*} [NormedAddCommGroup F] {f : R2 → F} {p : ENNReal}
    (hf : AEStronglyMeasurable f μT) (hper : IsTorusPeriodic f) :
    eLpNorm (f ∘ X) p μT = eLpNorm f p μT := by
  have heq : f ∘ X = f ∘ (torusWrap ∘ X) := by
    funext x
    exact (hper.eq_torusWrap (X x)).symm
  rw [heq]
  exact eLpNorm_comp_measurePreserving hf hX

lemma TorusAreaPreserving.integral_comp {X : R2 → R2} (hX : TorusAreaPreserving X)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : R2 → F}
    (hf : AEStronglyMeasurable f μT) (hper : IsTorusPeriodic f) :
    (∫ x in torusBox, f (X x)) = ∫ x in torusBox, f x := by
  have heq : (fun x => f (X x)) = f ∘ (torusWrap ∘ X) := by
    funext x
    exact (hper.eq_torusWrap (X x)).symm
  rw [heq]
  have hm : AEStronglyMeasurable f (Measure.map (torusWrap ∘ X) μT) := by
    rw [hX.map_eq]
    exact hf
  have hi := integral_map hX.aemeasurable hm
  rw [hX.map_eq] at hi
  exact hi.symm

/-- Area-preserving representative maps and their inverse give the
signed push-forward law for the continuous lifted particle map. -/
theorem IsVorticityPushForward.of_torusInverse
    {X Y : ℝ → R2 → R2} {w₀ : R2 → ℝ} {T : ℝ}
    (hw₀ : Integrable w₀ μT)
    (hX : ∀ t ∈ Icc 0 T, TorusAreaPreserving (X t))
    (hY : ∀ t ∈ Icc 0 T, TorusAreaPreserving (Y t))
    (hinv : ∀ t ∈ Icc 0 T, ∀ᵐ a ∂μT, torusWrap (Y t (torusWrap (X t a))) = a) :
    IsVorticityPushForward T w₀ (fun t x => w₀ (torusWrap (Y t x))) X := by
  have hp := IsVorticityPushForward.of_measurePreservingInverse hw₀ hX hY hinv
  refine ⟨hp.integrable, ?_⟩
  intro t ht χ hχ hχper
  calc
    _ = ∫ a in torusBox, w₀ a * χ (torusWrap (X t a)) := hp.pairing t ht χ hχ hχper
    _ = _ := by simp only [hχper.eq_torusWrap]

end Euler2D

end
