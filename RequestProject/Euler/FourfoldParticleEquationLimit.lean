module

public import RequestProject.Euler.FourfoldRegularizedApproximation
public import RequestProject.Euler.RegularizedVelocityLimit
public import RequestProject.Euler.ParticleEquationLimit
public import RequestProject.Euler.BoundedParticleVelocity

/-!
# The actual fourfold-kernel systems converge to the original particle equation

Every smooth system remains an explicit witness, so additional symmetry
properties survive its selection.  The limiting kernel is the original
singular Biot--Savart kernel, with its original physical normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Euler2D

theorem tendstoUniformly_fourfoldRegularizedTorusVelocity {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    {W : ι → Lp ℝ 2 μT} {Z : Lp ℝ 2 μT} (hW : Tendsto W l (𝓝 Z))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i, ∀ᵐ y ∂μT, ‖W i y‖ ≤ B)
    (hZ : ∀ᵐ y ∂μT, ‖Z y‖ ≤ B) :
    TendstoUniformly (fun i => torusKernelAverage (W i) (fourfoldRegularizedTorusKernel (ε i) (hε i)))
      (torusKernelVelocity Z) l := by
  have htrue := tendstoUniformly_torusKernelVelocity_of_tendsto_L2 hW hB0 hB hZ
  have herr : Tendsto (fun i => B * fourfoldRegularizedTorusKernelL1Error (ε i) (hε i)) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_fourfoldRegularizedTorusKernel_L1 ε hε hlim).const_mul B
  have heps : ∀ᶠ i in l, ε i ≤ 1 := by
    filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hi
    exact hi.le
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  have hnear := Metric.tendstoUniformly_iff.mp htrue (δ / 2) (by linarith)
  filter_upwards [heps, hnear, herr.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < δ / 2))]
    with i hi hnear herr x
  have hb := norm_fourfoldRegularizedTorusVelocity_error_le (hε i) hi
    (Lp.aestronglyMeasurable _) (hB i) x
  have ht := hnear x
  rw [dist_eq_norm] at ht ⊢
  rw [norm_sub_rev] at hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ (torusKernelVelocity (W i) x) _).trans_lt
    ((add_lt_add ht (hb.trans_lt herr)).trans_eq (by ring))

lemma fourfoldRegularizedParticleVelocity_eq_transportAverage (f : Lp ℝ 2 μT)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    {ε T : ℝ} (hε : 0 < ε) {L M : ℝ≥0}
    (S : SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel ε hε) w T L M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (x : R2) :
    S.velocity t x = torusKernelAverage (torusTransportL2 f (S.backward t) (S.backward_area t))
      (fourfoldRegularizedTorusKernel ε hε) x := by
  rw [S.transported_integral t ht x]
  apply integral_congr_ae
  have hpull := (S.backward_area t).quasiMeasurePreserving.ae_eq_comp hwf
  filter_upwards [torusTransportL2_ae f (S.backward t) (S.backward_area t), hpull] with y hy hw
  simp only [Function.comp_apply] at hw
  rw [hy]
  rw [hw]

theorem tendstoUniformly_fourfoldRegularizedParticleVelocity (f : Lp ℝ 2 μT)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {T : ℝ} {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel (ε n) (hε n)) w T (L n) (M n))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {Y : R2 → R2} (hY : TorusAreaPreserving Y)
    (hlim : ∀ᵐ a ∂μT, Tendsto (fun n => (S n).backward t a) atTop (𝓝 (Y a))) :
    TendstoUniformly (fun n => (S n).velocity t)
      (torusKernelVelocity (torusTransportL2 f Y hY)) atTop := by
  let W (n : ℕ) := torusTransportL2 f ((S n).backward t) ((S n).backward_area t)
  have hW : Tendsto W atTop (𝓝 (torusTransportL2 f Y hY)) :=
    tendsto_torusTransportL2_of_ae_tendsto f (fun n => (S n).backward_area t) hY hlim
  have hboundW (n : ℕ) : ∀ᵐ a ∂μT, ‖W n a‖ ≤ B :=
    norm_torusTransportL2_ae_le f hB _ _
  have hboundY : ∀ᵐ a ∂μT, ‖torusTransportL2 f Y hY a‖ ≤ B :=
    norm_torusTransportL2_ae_le f hB Y hY
  have he : (fun n => (S n).velocity t) =
      fun n => torusKernelAverage (W n) (fourfoldRegularizedTorusKernel (ε n) (hε n)) := by
    funext n x
    exact fourfoldRegularizedParticleVelocity_eq_transportAverage f hwf (hε n) (S n) ht x
  rw [he]
  exact tendstoUniformly_fourfoldRegularizedTorusVelocity ε hε hεlim hW hB0 hboundW hboundY

theorem tendsto_fourfoldRegularizedParticleVelocity_along_positions (f : Lp ℝ 2 μT)
    {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {T : ℝ} {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel (ε n) (hε n)) w T (L n) (M n))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) {Y : R2 → R2} (hY : TorusAreaPreserving Y)
    (hlim : ∀ᵐ a ∂μT, Tendsto (fun n => (S n).backward t a) atTop (𝓝 (Y a)))
    {a : ℕ → R2} {b : R2} (ha : Tendsto a atTop (𝓝 b)) :
    Tendsto (fun n => (S n).velocity t (a n)) atTop
      (𝓝 (torusKernelVelocity (torusTransportL2 f Y hY) b)) := by
  have hv := tendstoUniformly_fourfoldRegularizedParticleVelocity f hwf ε hε hεlim S hB0 hB ht hY hlim
  have hc := continuous_torusKernelVelocity (Lp.aestronglyMeasurable (torusTransportL2 f Y hY))
    (norm_torusTransportL2_ae_le f hB Y hY)
  exact hv.tendsto_comp hc.continuousAt ha

theorem fourfoldParticleSystem_integral_eq_of_tendsto
    (f : Lp ℝ 2 μT) {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    {T B : ℝ} (hT : 0 ≤ T)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel (ε n) (hε n)) w T (L n) (M n))
    (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    {F : Icc (0 : ℝ) T × R2 → R2} {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t))
    (hForward : ∀ (t : Icc (0 : ℝ) T) a,
      Tendsto (fun n => (S n).forward t a) atTop (𝓝 (F (t, a))))
    (hBackward : ∀ (t : Icc (0 : ℝ) T), ∀ᵐ a ∂μT,
      Tendsto (fun n => (S n).backward t a) atTop (𝓝 (Y t a)))
    (t : Icc (0 : ℝ) T) (a : R2) :
    F (t, a) = a + ∫ s in (0 : ℝ)..(t : ℝ),
      clampedParticleDerivative hT
        (fun r x => particleVelocityRepresentative f Y hY r x)
        (fun r x => F (r, x)) s a := by
  let gn (n : ℕ) (s : ℝ) := (S n).velocity s ((S n).forward s a)
  let g (s : ℝ) := clampedParticleDerivative hT
    (fun r x => particleVelocityRepresentative f Y hY r x) (fun r x => F (r, x)) s a
  have hw : AEStronglyMeasurable w μT := (Lp.aestronglyMeasurable f).congr hwf.symm
  have hwB : ∀ᵐ a ∂μT, ‖w a‖ ≤ B := by
    filter_upwards [hwf, hB] with a ha hba
    simpa only [ha] using hba
  obtain ⟨_C, V, _hC, _hV0, hV, _hlip⟩ :=
    exists_uniform_bounds_fourfoldRegularizedFamily ε hε hε1 S hw hB0 hwB
  have hgnc (n : ℕ) : Continuous (gn n) :=
    (S n).bounded.continuous.comp
      (continuous_id.prodMk ((S n).forward_continuous.comp
        (continuous_id.prodMk continuous_const)))
  have hgnbound (n : ℕ) :
      ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T), ‖gn n s‖ ≤ V := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hV n s hs _
  have hgnpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    have hp := tendsto_fourfoldRegularizedParticleVelocity_along_positions f hwf ε hε hεlim S
      hB0 hB hs (hY s) (hBackward ⟨s, hs⟩) (hForward ⟨s, hs⟩ a)
    have hg : g s = torusKernelVelocity (torusTransportL2 f (Y s) (hY s)) (F (⟨s, hs⟩, a)) := by
      dsimp only [g, clampedParticleDerivative]
      rw [projIcc_of_mem hT hs]
      rfl
    rw [hg]
    exact hp
  have hgnlim : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) T),
      Tendsto (fun n => gn n s) atTop (𝓝 (g s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hgnpoint s hs
  have hXlim (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      Tendsto (fun n => (S n).forward s a) atTop (𝓝 (F (projIcc 0 T hT s, a))) := by
    simpa only [projIcc_of_mem hT hs] using hForward ⟨s, hs⟩ a
  have heq := particle_integral_eq_of_tendsto
    (Xn := fun n s => (S n).forward s a)
    (X := fun s => F (projIcc 0 T hT s, a)) (gn := gn) (g := g)
    (fun n => (S n).initial a) (fun n s hs => (S n).derivative s hs a)
    (fun n => (hgnc n).aestronglyMeasurable) hgnbound hgnlim hXlim t.property
  simpa only [projIcc_of_mem hT t.property] using heq

theorem fourfoldParticleSystem_subseq_integral_eq
    (f : Lp ℝ 2 μT) {w : R2 → ℝ} (hwf : w =ᵐ[μT] (f : R2 → ℝ))
    {T B : ℝ} (hT : 0 ≤ T)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hεlim : Tendsto ε atTop (𝓝 0)) {L M : ℕ → ℝ≥0}
    (S : ∀ n, SmoothRegularizedParticleSystem (fourfoldRegularizedTorusKernel (ε n) (hε n)) w T (L n) (M n))
    (hB0 : 0 ≤ B) (hB : ∀ᵐ a ∂μT, ‖f a‖ ≤ B)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    {F : Icc (0 : ℝ) T × R2 → R2} {Y : ℝ → R2 → R2}
    (hY : ∀ t, TorusAreaPreserving (Y t))
    (hForward : ∀ (t : Icc (0 : ℝ) T) a,
      Tendsto (fun n => (S (φ n)).forward t a) atTop (𝓝 (F (t, a))))
    (hBackward : ∀ (t : Icc (0 : ℝ) T), ∀ᵐ a ∂μT,
      Tendsto (fun n => (S (φ n)).backward t a) atTop (𝓝 (Y t a)))
    (t : Icc (0 : ℝ) T) (a : R2) :
    F (t, a) = a + ∫ s in (0 : ℝ)..(t : ℝ),
      clampedParticleDerivative hT
        (fun r x => particleVelocityRepresentative f Y hY r x)
        (fun r x => F (r, x)) s a :=
  fourfoldParticleSystem_integral_eq_of_tendsto f hwf hT (ε ∘ φ) (fun n => hε (φ n))
    (fun n => hε1 (φ n)) (hεlim.comp hφ.tendsto_atTop) (fun n => S (φ n))
    hB0 hB hY hForward hBackward t a

end Euler2D

end
