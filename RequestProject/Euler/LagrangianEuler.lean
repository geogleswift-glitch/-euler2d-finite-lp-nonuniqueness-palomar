module

public import RequestProject.Euler.VorticityMomentum
public import RequestProject.Euler.TorusTransport
public import RequestProject.Euler.BiotSavartL2
public import RequestProject.Euler.TorusTransportContinuity
public import RequestProject.Euler.DatumCurlSeries

/-!
# The original momentum equation from actual particle trajectories

The driving continuous velocity agrees almost everywhere with the
constructed L² velocity. The particle ODE gives the vorticity equation,
which is then converted to the original momentum weak formulation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Euler2D

/-- Actual trajectories and their signed push-forward vorticity imply
the original weak Euler equation, including its actual initial value. -/
theorem weakEuler_of_particle_flow {T : ℝ} (hT : 0 ≤ T)
    {U : ℝ → L2T} {w : ℝ → R2 → ℝ} {w₀ : R2 → ℝ}
    {X v : ℝ → R2 → R2}
    (hU : ContinuousOn U (Icc 0 T))
    (hdiv : ∀ t ∈ Icc 0 T, DivFree (U t))
    (hw : ∀ t ∈ Icc 0 T, MemLp (w t) 2 μT)
    (hc : ∀ t ∈ Icc 0 T, IsCurl (U t) (w t))
    (hmean : ∀ t ∈ Icc 0 T, ∫ x in torusBox, U t x = 0)
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hvper : ∀ t, IsTorusPeriodic (v t))
    (hw₀ : Integrable w₀ μT)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => X s a) (v t (X t a)) t)
    (hpush : IsVorticityPushForward T w₀ w X)
    (hrep : ∀ t ∈ Icc 0 T, U t =ᵐ[μT] v t) :
    IsWeakEulerSolution T (U 0) U := by
  apply weakEuler_of_weakVorticity hT hU hdiv hw hc hmean
  intro χ hχ
  have hweak := (flow_weak_vorticity_spacetime hT hX hv hvper hχ hw₀ hinit hflow hpush).2
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hχzero : Continuous (χ 0) := hχ.smooth.continuous.comp
    (continuous_const.prodMk continuous_id)
  have hinitial : (∫ x in torusBox, w 0 x * χ 0 x) = ∫ x in torusBox, w₀ x * χ 0 x := by
    rw [hpush.pairing 0 hzero (χ 0) hχzero (hχ.periodic 0)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_torusBox] with x hx
    rw [hinit x hx]
  have htime : (∫ t in (0 : ℝ)..T, ∫ x in torusBox, w t x *
      (deriv (fun s => χ s x) t + ∑ i : Fin 2, U t x i * pd i (χ t) x)) =
      ∫ t in (0 : ℝ)..T, ∫ x in torusBox, w t x *
        (deriv (fun s => χ s x) t + ∑ i : Fin 2, v t x i * pd i (χ t) x) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    apply integral_congr_ae
    filter_upwards [hrep t ht'] with x hx
    rw [hx]
  rw [htime, hinitial]
  exact hweak

/-- Canonical transported vorticity, represented in the actual box L². -/
def particleCurlL2 (f : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) : Lp ℝ 2 μT :=
  Lp.compMeasurePreserving (torusWrap ∘ Y t) (hY t) f

lemma particleCurlL2_ae (f : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    particleCurlL2 f Y hY t =ᵐ[μT] fun x => f (torusWrap (Y t x)) :=
  Lp.coeFn_compMeasurePreserving f (hY t)

lemma integral_particleCurlL2 (f : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) :
    (∫ x in torusBox, particleCurlL2 f Y hY t x) = ∫ x in torusBox, f x := by
  calc
    _ = ∫ x in torusBox, f (torusWrap (Y t x)) := integral_congr_ae (particleCurlL2_ae f Y hY t)
    _ = ∫ x, f x ∂Measure.map (torusWrap ∘ Y t) μT :=
      (integral_map (hY t).aemeasurable (by rw [(hY t).map_eq]; exact Lp.aestronglyMeasurable f)).symm
    _ = _ := by rw [(hY t).map_eq]

def particleVelocity (f : Lp ℝ 2 μT) (Y : ℝ → R2 → R2)
    (hY : ∀ t, TorusAreaPreserving (Y t)) (t : ℝ) : L2T :=
  biotSavartL2 (particleCurlL2 f Y hY t)

lemma continuous_particleCurlL2 (f : Lp ℝ 2 μT) {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t)) (hYc : Continuous (Function.uncurry Y)) :
    Continuous (particleCurlL2 f Y hY) :=
  continuous_torusTransportL2 f hYc hY

lemma continuous_particleVelocity (f : Lp ℝ 2 μT) {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t)) (hYc : Continuous (Function.uncurry Y)) :
    Continuous (particleVelocity f Y hY) :=
  biotSavartL2.continuous.comp (continuous_particleCurlL2 f hY hYc)

lemma particleCurlL2_initial (f : Lp ℝ 2 μT) {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t)) {X : R2 → R2}
    (hinit : ∀ a ∈ torusBox, X a = a)
    (hinv : ∀ᵐ a ∂μT, torusWrap (Y 0 (torusWrap (X a))) = a) :
    particleCurlL2 f Y hY 0 = f := by
  apply Lp.ext
  filter_upwards [particleCurlL2_ae f Y hY 0, hinv,
    ae_restrict_mem measurableSet_torusBox] with x hx hi hbox
  rw [hinit x hbox, show torusWrap x = x from torusRep_torusProj hbox] at hi
  rw [hx, hi]

/-- The exact transported Lᵠ norm gives a genuine uniform curl bound for
the constructed velocity, without assuming any Sobolev estimate. -/
theorem curlBoundedBy_particleVelocity {q : ENNReal} [Fact (1 ≤ q)] (hq : 2 ≤ q)
    (f : Lp ℝ q μT) (hf : (∫ x in torusBox, f x) = 0)
    (Y : ℝ → R2 → R2) (hY : ∀ t, TorusAreaPreserving (Y t)) (T : ℝ) :
    CurlBoundedBy T q ‖f‖ (particleVelocity (scalarLpLowerToTwo hq f) Y hY) := by
  have hm : (∫ x in torusBox, scalarLpLowerToTwo hq f x) = 0 :=
    (integral_congr_ae (scalarLpLowerToTwo_ae hq f)).trans hf
  intro t _
  let w := fun x => f (torusWrap (Y t x))
  have hwae : particleCurlL2 (scalarLpLowerToTwo hq f) Y hY t =ᵐ[μT] w :=
    (particleCurlL2_ae _ Y hY t).trans
      ((hY t).quasiMeasurePreserving.ae_eq_comp (scalarLpLowerToTwo_ae hq f))
  refine ⟨w, (Lp.memLp f).comp_measurePreserving (hY t), ?_, ?_⟩
  · exact (isCurl_biotSavartL2 _ ((integral_particleCurlL2 _ Y hY t).trans hm)).congr_ae
      (EventuallyEq.refl _ _) hwae
  · change (eLpNorm ((f : R2 → ℝ) ∘ (torusWrap ∘ Y t)) q μT).toReal ≤ ‖f‖
    rw [eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) (hY t)]
    exact le_rfl

/-- The Biot–Savart construction automatically supplies divergence,
mean and the correct distributional vorticity to the particle theorem. -/
theorem weakEuler_of_biotSavart_particle_flow {T : ℝ} (hT : 0 ≤ T)
    (f : Lp ℝ 2 μT) (hf : (∫ x in torusBox, f x) = 0)
    {X Y v : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t))
    (hYc : Continuous (Function.uncurry Y))
    (hX : Continuous (Function.uncurry X))
    (hv : Continuous (Function.uncurry v)) (hvper : ∀ t, IsTorusPeriodic (v t))
    (hXmp : ∀ t ∈ Icc 0 T, TorusAreaPreserving (X t))
    (hinv : ∀ t ∈ Icc 0 T, ∀ᵐ a ∂μT, torusWrap (Y t (torusWrap (X t a))) = a)
    (hinit : ∀ a ∈ torusBox, X 0 a = a)
    (hflow : ∀ a ∈ torusBox, ∀ t ∈ Icc 0 T,
      HasDerivAt (fun s => X s a) (v t (X t a)) t)
    (hrep : ∀ t ∈ Icc 0 T, particleVelocity f Y hY t =ᵐ[μT] v t) :
    IsWeakEulerSolution T (particleVelocity f Y hY 0) (particleVelocity f Y hY) := by
  have hw₀ : Integrable (f : R2 → ℝ) μT := (Lp.memLp f).integrable (by norm_num)
  apply weakEuler_of_particle_flow hT (continuous_particleVelocity f hY hYc).continuousOn
    (fun t _ => divFree_biotSavartL2 _) _ _ (fun t _ => integral_biotSavartL2 _)
    hX hv hvper hw₀ hinit hflow
    (IsVorticityPushForward.of_torusInverse hw₀ hXmp (fun t _ => hY t) hinv) hrep
  · intro t _
    exact (Lp.memLp f).comp_measurePreserving (hY t)
  · intro t _
    have hc := isCurl_biotSavartL2 (particleCurlL2 f Y hY t)
      ((integral_particleCurlL2 f Y hY t).trans hf)
    exact hc.congr_ae (EventuallyEq.refl _ _) (particleCurlL2_ae f Y hY t)

end Euler2D

end
