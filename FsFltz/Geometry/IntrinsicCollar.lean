import FsFltz.Geometry.IntrinsicCollarLocal
import FsFltz.Geometry.IntrinsicCollarEmbedding
import FsFltz.Geometry.IntrinsicCollarUniqueness

/-!
# Native one-sided collar trajectories from local coefficient extensions

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. The local coefficients extend smoothly across the chart
boundary as required by the source convention (lines 119–122 and 141).
Their agreement with the intrinsic field is an explicit equation using
the actual differential of a native chart. No collar, ambient extension
manifold, or completed flow is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

variable {k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The half-open native ODE supplies the right derivative used by
one-sided uniqueness, including the initial boundary time. -/
theorem right_derivative_of_integralCurveOn
    {γ : ℝ → M} {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x} {δ t : ℝ}
    (hγ : IsMIntegralCurveOn γ Z (Ico 0 δ)) (ht : t ∈ Ico 0 δ) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1)) γ (Ici t) t
      (ContinuousLinearMap.toSpanSingleton ℝ (Z (γ t))) :=
  (hγ t ht).mono_of_mem_nhdsWithin
    (mem_of_superset (Ico_mem_nhdsGE ht.2) (Ico_subset_Ico_left ht.1))

/-- Native one-sided integral curves with the same initial point have
the same germ. Continuity and right derivatives are derived from the
actual integral-curve equations; common chart containment is constructed. -/
theorem exists_pos_eqOn_of_native_integralCurveOn
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {f : Model (k + 1) → Model (k + 1)} {U : Set (Model (k + 1))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hcoeff : ∀ x ∈ e.source, e.extend (𝓡∂ (k + 1)) x ∈ U →
      f (e.extend (𝓡∂ (k + 1)) x) =
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
          (e.extend (𝓡∂ (k + 1))) x (Z x))
    {γ η : ℝ → M} {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    (hγ : IsMIntegralCurveOn γ Z (Ico 0 δ))
    (hη : IsMIntegralCurveOn η Z (Ico 0 T))
    (hx : γ 0 ∈ e.source) (hxU : e.extend (𝓡∂ (k + 1)) (γ 0) ∈ U)
    (hzero : γ 0 = η 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < min δ T ∧ EqOn γ η (Icc 0 ε) := by
  have hb : 0 < min δ T / 2 := half_pos (lt_min hδ hT)
  have hbδ : min δ T / 2 < δ := lt_of_lt_of_le (half_lt_self (lt_min hδ hT))
    (min_le_left _ _)
  have hbT : min δ T / 2 < T := lt_of_lt_of_le (half_lt_self (lt_min hδ hT))
    (min_le_right _ _)
  have hsδ : Icc 0 (min δ T / 2) ⊆ Ico 0 δ :=
    fun _ ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbδ⟩
  have hsT : Icc 0 (min δ T / 2) ⊆ Ico 0 T :=
    fun _ ht => ⟨ht.1, lt_of_le_of_lt ht.2 hbT⟩
  obtain ⟨ε, hε, hεb, heq⟩ := exists_pos_eqOn_of_native_right_ode he hU hf hcoeff hb
    (hγ.continuousOn.mono hsδ) (hη.continuousOn.mono hsT)
    (fun t ht => right_derivative_of_integralCurveOn hγ (hsδ (Ico_subset_Icc_self ht)))
    (fun t ht => right_derivative_of_integralCurveOn hη (hsT (Ico_subset_Icc_self ht)))
    hx hxU hzero
  exact ⟨ε, hε, hεb.trans (half_lt_self (lt_min hδ hT)), heq⟩

/-- Pull back an actual coordinate ODE through a native chart. The inverse
differential identity holds at boundary points as well as interior points;
only a within derivative on the supplied time set is asserted. -/
theorem hasMFDerivWithinAt_chart_symm
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    {Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x}
    {f : Model (k + 1) → Model (k + 1)} {γ : ℝ → Model (k + 1)}
    {s : Set ℝ} {t : ℝ} (ht : t ∈ s)
    (hγ : HasDerivWithinAt γ (f (γ t)) s t)
    (hmaps : MapsTo γ s (e.extend (𝓡∂ (k + 1))).target)
    (hcoeff : f (γ t) =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (e.extend (𝓡∂ (k + 1)))
        ((e.extend (𝓡∂ (k + 1))).symm (γ t))
        (Z ((e.extend (𝓡∂ (k + 1))).symm (γ t)))) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) (𝓡∂ (k + 1))
      (fun r => (e.extend (𝓡∂ (k + 1))).symm (γ r)) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (Z ((e.extend (𝓡∂ (k + 1))).symm (γ t)))) := by
  have he₁ : e ∈ IsManifold.maximalAtlas (𝓡∂ (k + 1)) 1 M :=
    IsManifold.subset_maximalAtlas he
  have hd := (mdifferentiableWithinAt_extend_symm he₁ (hmaps ht)).hasMFDerivWithinAt
  have hγm : HasMFDerivWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model (k + 1)) γ s t
      (ContinuousLinearMap.toSpanSingleton ℝ (f (γ t))) :=
    hasMFDerivWithinAt_iff_hasFDerivWithinAt.mpr hγ.hasFDerivWithinAt
  apply (hd.comp t hγm (fun r hr => e.extend_target_subset_range (hmaps hr))).congr_mfderiv
  have hi := mfderivWithin_extend_symm_comp_mfderiv_extend he₁ (hmaps ht)
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderivWithin 𝓘(ℝ, Model (k + 1)) (𝓡∂ (k + 1))
    (e.extend (𝓡∂ (k + 1))).symm (range (𝓡∂ (k + 1))) (γ t) (r • f (γ t)) =
      r • Z ((e.extend (𝓡∂ (k + 1))).symm (γ t))
  rw [hcoeff, map_smul]
  exact congrArg (fun v => r • v)
    (congrArg (fun A => A (Z ((e.extend (𝓡∂ (k + 1))).symm (γ t)))) hi)

/-- Construct a native local collar, jointly smooth up to time zero,
from the explicitly extended coefficients of the intrinsic field. Its
one-sided strip is an open embedding. The trajectories solve the native
ODE, start at the chart's boundary inclusion, and lie on the intrinsic
boundary exactly at time zero. -/
theorem exists_native_local_collar
    {e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1))}
    (he : e ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (Z : (x : M) → TangentSpace (𝓡∂ (k + 1)) x)
    {f : Model (k + 1) → Model (k + 1)} {U : Set (Model (k + 1))} {u : Model k}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hu : boundaryInsert k u ∈ U)
    (htarget : ∀ y ∈ U, 0 ≤ y 0 → y ∈ (e.extend (𝓡∂ (k + 1))).target)
    (hcoeff : ∀ y ∈ U, 0 ≤ y 0 → f y =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) (e.extend (𝓡∂ (k + 1)))
        ((e.extend (𝓡∂ (k + 1))).symm y)
        (Z ((e.extend (𝓡∂ (k + 1))).symm y)))
    (hin : 0 < f (boundaryInsert k u) 0) :
    ∃ (γ : ℝ × Model k → M) (V : Set (Model k)) (δ : ℝ),
      IsOpen V ∧ u ∈ V ∧ 0 < δ ∧
      ContMDiffOn 𝓘(ℝ, ℝ × Model k) (𝓡∂ (k + 1)) ∞ γ (Ico 0 δ ×ˢ V) ∧
      Topology.IsOpenEmbedding (fun p : Ico 0 δ ×ˢ V => γ p.val) ∧
      (∀ p ∈ Ico 0 δ ×ˢ V, ∃ g : M → ℝ × Model k,
        ContMDiffAt (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ × Model k) ∞ g (γ p) ∧
          ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ V] p, g (γ q) = q) ∧
      (∀ v ∈ V, γ (0, v) = e.symm (IntrinsicBoundary.halfSpaceInsert k v)) ∧
      (∀ v ∈ V, IsMIntegralCurveOn (fun t => γ (t, v)) Z (Ico 0 δ)) ∧
      (∀ v ∈ V, ∀ t ∈ Ico 0 δ, γ (t, v) ∈ e.source ∧
        ((𝓡∂ (k + 1)).IsBoundaryPoint (γ (t, v)) ↔ t = 0)) ∧
      ∀ v ∈ V, ∀ (η : ℝ → M) (T : ℝ), 0 < T →
        IsMIntegralCurveOn η Z (Ico 0 T) → γ (0, v) = η 0 →
        ∃ ε : ℝ, 0 < ε ∧ ε < min δ T ∧
          EqOn (fun t => γ (t, v)) η (Icc 0 ε) := by
  obtain ⟨c, V, δ, hc, hV, huV, hδ, hzero, hinj, hloc, hode⟩ :=
    exists_halfSpace_collar hU hf hu hin
  let γ : ℝ × Model k → M := fun p => (e.extend (𝓡∂ (k + 1))).symm (c p)
  have htime {t : ℝ} (ht : t ∈ Ico 0 δ) : t ∈ Ioo (-δ) δ :=
    ⟨by linarith [ht.1], ht.2⟩
  have hmaps {v : Model k} (hv : v ∈ V) {t : ℝ} (ht : t ∈ Ico 0 δ) :
      c (t, v) ∈ (e.extend (𝓡∂ (k + 1))).target :=
    htarget _ (hode v hv t (htime ht)).1
      ((hode v hv t (htime ht)).2.2.1.mpr ht.1)
  have he_smooth : e ∈ IsManifold.maximalAtlas (𝓡∂ (k + 1)) ∞ M :=
    IsManifold.subset_maximalAtlas he
  have hcurve (v : Model k) (hv : v ∈ V) :
      IsMIntegralCurveOn (fun t => γ (t, v)) Z (Ico 0 δ) := by
    intro t ht
    apply hasMFDerivWithinAt_chart_symm he ht
      (hode v hv t (htime ht)).2.1.hasDerivWithinAt (fun s hs => hmaps hv hs)
    exact hcoeff _ (hode v hv t (htime ht)).1
      ((hode v hv t (htime ht)).2.2.1.mpr ht.1)
  refine ⟨γ, V, δ, hV, huV, hδ, ?_, ?_, ?_, ?_, hcurve, ?_, ?_⟩
  · apply (contMDiffOn_extend_symm he_smooth).comp hc.contMDiff.contMDiffOn
    intro p hp
    have h := hmaps hp.2 hp.1
    rw [OpenPartialHomeomorph.extend_target] at h
    exact ⟨(𝓡∂ (k + 1)).symm (c p), h.1, (𝓡∂ (k + 1)).right_inv h.2⟩
  · have hhalf := isOpenEmbedding_halfSpace_restrict hδ hV hinj hloc
      (fun p hp => (hode p.2 hp.2 p.1 hp.1).2.2.1)
    have hh (p : Ico 0 δ ×ˢ V) : (𝓡∂ (k + 1)).symm (c p.val) ∈ e.target := by
      have h := hmaps p.property.2 p.property.1
      rw [OpenPartialHomeomorph.extend_target] at h
      exact h.1
    let a : (Ico 0 δ ×ˢ V) → e.target :=
      fun p => ⟨(𝓡∂ (k + 1)).symm (c p.val), hh p⟩
    have ha : Topology.IsOpenEmbedding a :=
      e.open_target.isOpenEmbedding_subtypeVal.of_comp a hhalf
    exact e.symm.isOpenEmbedding_restrict.comp ha
  · intro p hp
    obtain ⟨d, hpd, heq⟩ := hloc ⟨p, htime hp.1, hp.2⟩
    let g : M → ℝ × Model k := d.symm ∘ e.extend (𝓡∂ (k + 1))
    have hs : γ p ∈ e.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (e.extend (𝓡∂ (k + 1))).map_target (hmaps hp.2 hp.1)
    have hc_inv : ContMDiffAt 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, ℝ × Model k) ∞
        d.symm (c p) := by
      rw [heq hpd]
      exact d.symm.contMDiffOn.contMDiffAt (d.open_target.mem_nhds (d.map_source hpd))
    refine ⟨g, ?_, ?_⟩
    · have hext := e.contMDiffAt_extend he_smooth hs
      apply ContMDiffAt.comp (γ p) (f := e.extend (𝓡∂ (k + 1))) _ hext
      change ContMDiffAt _ _ _ d.symm ((e.extend (𝓡∂ (k + 1)))
        ((e.extend (𝓡∂ (k + 1))).symm (c p)))
      rw [(e.extend (𝓡∂ (k + 1))).right_inv (hmaps hp.2 hp.1)]
      exact hc_inv
    · have hnd : d.source ∈ 𝓝[Ico 0 δ ×ˢ V] p :=
        mem_nhdsWithin_of_mem_nhds (d.open_source.mem_nhds hpd)
      filter_upwards [self_mem_nhdsWithin, hnd] with q hq hdq
      change d.symm ((e.extend (𝓡∂ (k + 1)))
        ((e.extend (𝓡∂ (k + 1))).symm (c q))) = q
      rw [(e.extend (𝓡∂ (k + 1))).right_inv (hmaps hq.2 hq.1), heq hdq]
      exact d.left_inv hdq
  · intro v _
    change e.symm ((𝓡∂ (k + 1)).symm (c (0, v))) = _
    rw [hzero, IntrinsicBoundary.model_symm_boundaryInsert]
  · intro v hv t ht
    have hs : γ (t, v) ∈ e.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (e.extend (𝓡∂ (k + 1))).map_target (hmaps hv ht)
    refine ⟨hs, ?_⟩
    rw [IntrinsicBoundary.isBoundaryPoint_iff_chart_zero he hs]
    have hcoord : (e (γ (t, v))).val = c (t, v) :=
      (e.extend (𝓡∂ (k + 1))).right_inv (hmaps hv ht)
    rw [hcoord]
    have hpos := (hode v hv t (htime ht)).2.2.2
    have hnonneg := (hode v hv t (htime ht)).2.2.1.mpr ht.1
    constructor
    · intro hz
      have : ¬ 0 < t := fun h => by simpa only [hz, lt_self_iff_false] using hpos.mpr h
      exact le_antisymm (le_of_not_gt this) ht.1
    · intro hz
      exact le_antisymm (le_of_not_gt (by simpa only [hz, lt_self_iff_false, iff_false] using hpos))
        hnonneg
  · intro v hv η T hT hη hzero
    have htzero : (0 : ℝ) ∈ Ico 0 δ := ⟨le_rfl, hδ⟩
    have hx : γ (0, v) ∈ e.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (e.extend (𝓡∂ (k + 1))).map_target (hmaps hv htzero)
    have hxU : e.extend (𝓡∂ (k + 1)) (γ (0, v)) ∈ U := by
      change e.extend (𝓡∂ (k + 1)) ((e.extend (𝓡∂ (k + 1))).symm (c (0, v))) ∈ U
      rw [(e.extend (𝓡∂ (k + 1))).right_inv (hmaps hv htzero)]
      exact (hode v hv 0 (htime htzero)).1
    apply exists_pos_eqOn_of_native_integralCurveOn he hU hf _ hδ hT
      (hcurve v hv) hη hx hxU hzero
    intro x hx hxU
    have hsx : x ∈ (e.extend (𝓡∂ (k + 1))).source := by
      simpa only [OpenPartialHomeomorph.extend_source] using hx
    have hn : 0 ≤ (e.extend (𝓡∂ (k + 1)) x) 0 := (e x).property
    have H := hcoeff _ hxU hn
    rw [(e.extend (𝓡∂ (k + 1))).left_inv hsx] at H
    exact H

end FsFltz.Geometry.IntrinsicCollar
