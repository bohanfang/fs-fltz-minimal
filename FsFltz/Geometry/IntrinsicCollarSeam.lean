import FsFltz.Geometry.IntrinsicCollarGlobalUniqueness
import FsFltz.Geometry.IntrinsicCollarCoefficients

/-!
# Two-sided coordinate germs of the same native collar

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and
`sec:lean`, lines 783–814. Smooth extension across boundaries is required
at lines 119–122 and 141. The extended coordinate evolution is constructed
from scalar germs of the actual native field. Whole-interval native ODE
uniqueness identifies its nonnegative-time restriction with the given collar,
on one rectangle uniform in the boundary variable.

No matching two-sided germ or negative-time native trajectory is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicCollar

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Every seam of the same native collar has a constructed smooth two-sided
coordinate germ. Its positive-time agreement with the collar holds on a
single rectangle, rather than on times depending on the boundary point.
The extended map is locally invertible and its normal coordinate has exactly
the sign of time. Only scalar source extension germs and inwardness are input. -/
theorem exists_seam_coordinate_germ_of_scalar_extensions
    (c : IntrinsicBoundary.Chart k M) {x : IntrinsicBoundary.Point k M}
    (hx : x ∈ c.chart.source)
    (Z : (z : M) → TangentSpace (𝓡∂ (k + 1)) z)
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ y, C (0, y) = y.val)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ))
    (hscalar : ∀ i : Fin (k + 1),
      ∃ (f : Model (k + 1) → ℝ) (U : Set (Model (k + 1))),
        IsOpen U ∧ c.ambient.extend (𝓡∂ (k + 1)) x.val ∈ U ∧
        ContDiffOn ℝ ∞ f U ∧
        f =ᶠ[𝓝[(c.ambient.extend (𝓡∂ (k + 1))).target]
          (c.ambient.extend (𝓡∂ (k + 1)) x.val)]
          (fun y => (show Model (k + 1) from
            mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (c.ambient.extend (𝓡∂ (k + 1)))
              ((c.ambient.extend (𝓡∂ (k + 1))).symm y)
                (Z ((c.ambient.extend (𝓡∂ (k + 1))).symm y))) i))
    (hin : 0 < (show Model (k + 1) from
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (c.ambient.extend (𝓡∂ (k + 1))) x.val (Z x.val)) 0) :
    ∃ (g : ℝ × Model k → Model (k + 1)) (V : Set (Model k)) (ε : ℝ),
      ContDiff ℝ ∞ g ∧ IsOpen V ∧ c.chart x ∈ V ∧ V ⊆ c.chart.target ∧
      0 < ε ∧ ε ≤ δ ∧ (∀ v, g (0, v) = boundaryInsert k v) ∧
      InjOn g (Ioo (-ε) ε ×ˢ V) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × Model k) 𝓘(ℝ, Model (k + 1)) ∞ g
        (Ioo (-ε) ε ×ˢ V) ∧
      (∀ v ∈ V, ∀ t ∈ Ioo (-ε) ε,
        (0 ≤ g (t, v) 0 ↔ 0 ≤ t) ∧ (0 < g (t, v) 0 ↔ 0 < t)) ∧
      ∀ v ∈ V, ∀ t ∈ Ico 0 ε,
        C (t, c.chart.symm v) ∈ c.ambient.source ∧
        c.ambient.extend (𝓡∂ (k + 1)) (C (t, c.chart.symm v)) = g (t, v) := by
  let e := c.ambient
  have hex : x.val ∈ e.source := by
    have h := hx
    rwa [c.source_eq] at h
  have hcoord : boundaryInsert k (c.chart x) = e.extend (𝓡∂ (k + 1)) x.val := by
    rw [c.toFun_eq x hx]
    apply boundaryInsert_drop
    exact (IntrinsicBoundary.isBoundaryPoint_iff_chart_zero c.mem_atlas hex).mp x.property
  obtain ⟨f, A, hA, hxA, hf, htarget, hcoeff⟩ :=
    exists_local_coefficients_of_scalar_extensions hex hscalar
  have hinf : 0 < f (boundaryInsert k (c.chart x)) 0 := by
    rw [hcoord, hcoeff _ hxA (e x.val).property,
      (e.extend (𝓡∂ (k + 1))).left_inv (by simpa only [e.extend_source] using hex)]
    exact hin
  obtain ⟨g, V₀, T, hg, hV₀, hxV₀, hT, hgzero, hginj, hgloc, hgode⟩ :=
    exists_halfSpace_collar hA hf (by rwa [hcoord]) hinf
  let V := V₀ ∩ c.chart.target
  let ε := min T δ
  have hε : 0 < ε := lt_min hT hδ
  have htime {t : ℝ} (ht : t ∈ Ico 0 T) : t ∈ Ioo (-T) T :=
    ⟨by linarith [ht.1], ht.2⟩
  have hmaps {v : Model k} (hv : v ∈ V₀) {t : ℝ} (ht : t ∈ Ico 0 T) :
      g (t, v) ∈ (e.extend (𝓡∂ (k + 1))).target :=
    htarget _ (hgode v hv t (htime ht)).1
      ((hgode v hv t (htime ht)).2.2.1.mpr ht.1)
  let γ : ℝ × Model k → M := fun p => (e.extend (𝓡∂ (k + 1))).symm (g p)
  have hγ (v : Model k) (hv : v ∈ V₀) :
      IsMIntegralCurveOn (fun t => γ (t, v)) Z (Ico 0 T) := by
    intro t ht
    apply hasMFDerivWithinAt_chart_symm c.mem_atlas ht
      (hgode v hv t (htime ht)).2.1.hasDerivWithinAt (fun s hs => hmaps hv hs)
    exact hcoeff _ (hgode v hv t (htime ht)).1
      ((hgode v hv t (htime ht)).2.2.1.mpr ht.1)
  have hγsource (v : Model k) (hv : v ∈ V₀) (t : ℝ) (ht : t ∈ Ico 0 T) :
      γ (t, v) ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using
      (e.extend (𝓡∂ (k + 1))).map_target (hmaps hv ht)
  have hγcoord (v : Model k) (hv : v ∈ V₀) (t : ℝ) (ht : t ∈ Ico 0 T) :
      e.extend (𝓡∂ (k + 1)) (γ (t, v)) = g (t, v) :=
    (e.extend (𝓡∂ (k + 1))).right_inv (hmaps hv ht)
  have hγzero (v : Model k) (hv : v ∈ V) : γ (0, v) = (c.chart.symm v).val := by
    change e.symm ((𝓡∂ (k + 1)).symm (g (0, v))) = _
    rw [hgzero, IntrinsicBoundary.model_symm_boundaryInsert]
    exact (c.invFun_eq v hv.2).symm
  have hmatch (v : Model k) (hv : v ∈ V) :
      EqOn (fun t => γ (t, v)) (fun t => C (t, c.chart.symm v)) (Ico 0 ε) := by
    apply eqOn_of_native_integralCurveOn_of_common_local_coefficients _
      (hγ v hv.1) (hode (c.chart.symm v))
      ((hγzero v hv).trans (hzero (c.chart.symm v)).symm)
    intro t ht _
    have htT : t ∈ Ico 0 T := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    refine ⟨e, c.mem_atlas, hγsource v hv.1 t htT, f, A, hA, hf, ?_, ?_⟩
    · rw [hγcoord v hv.1 t htT]
      exact (hgode v hv.1 t (htime htT)).1
    · intro z hz hzA
      have H := hcoeff _ hzA (e z).property
      rwa [(e.extend (𝓡∂ (k + 1))).left_inv
        (by simpa only [e.extend_source] using hz)] at H
  have hsub : Ioo (-ε) ε ×ˢ V ⊆ Ioo (-T) T ×ˢ V₀ := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    exact ⟨⟨lt_of_le_of_lt (neg_le_neg (min_le_left T δ)) ht.1,
      ht.2.trans_le (min_le_left _ _)⟩, hv.1⟩
  refine ⟨g, V, ε, hg, hV₀.inter c.chart.open_target,
    ⟨hxV₀, c.chart.map_source hx⟩, inter_subset_right, hε, min_le_right _ _,
    hgzero, hginj.mono hsub, ?_, ?_, ?_⟩
  · intro p
    exact hgloc ⟨p.val, hsub p.property⟩
  · intro v hv t ht
    exact (hgode v hv.1 t (hsub (show (t, v) ∈ Ioo (-ε) ε ×ˢ V from ⟨ht, hv⟩)).1).2.2
  · intro v hv t ht
    have htT : t ∈ Ico 0 T := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have heq : γ (t, v) = C (t, c.chart.symm v) := hmatch v hv ht
    rw [← heq]
    exact ⟨hγsource v hv.1 t htT, hγcoord v hv.1 t htT⟩

/-- A source scalar with an actual smooth chart extension acquires a smooth
two-sided germ along the same collar. Smoothness holds on one open
neighborhood at order infinity, and agreement holds on its entire native
half-strip. This is a local additional-data extension producer. -/
theorem exists_seam_scalar_germ_of_scalar_extensions
    (c : IntrinsicBoundary.Chart k M) {x : IntrinsicBoundary.Point k M}
    (hx : x ∈ c.chart.source)
    (Z : (z : M) → TangentSpace (𝓡∂ (k + 1)) z)
    (C : ℝ × IntrinsicBoundary.Point k M → M) {δ : ℝ} (hδ : 0 < δ)
    (hzero : ∀ y, C (0, y) = y.val)
    (hode : ∀ y, IsMIntegralCurveOn (fun t => C (t, y)) Z (Ico 0 δ))
    (hscalar : ∀ i : Fin (k + 1),
      ∃ (f : Model (k + 1) → ℝ) (U : Set (Model (k + 1))),
        IsOpen U ∧ c.ambient.extend (𝓡∂ (k + 1)) x.val ∈ U ∧
        ContDiffOn ℝ ∞ f U ∧
        f =ᶠ[𝓝[(c.ambient.extend (𝓡∂ (k + 1))).target]
          (c.ambient.extend (𝓡∂ (k + 1)) x.val)]
          (fun y => (show Model (k + 1) from
            mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (c.ambient.extend (𝓡∂ (k + 1)))
              ((c.ambient.extend (𝓡∂ (k + 1))).symm y)
                (Z ((c.ambient.extend (𝓡∂ (k + 1))).symm y))) i))
    (hin : 0 < (show Model (k + 1) from
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
        (c.ambient.extend (𝓡∂ (k + 1))) x.val (Z x.val)) 0)
    (φ : M → ℝ)
    (hφ : ∃ (β : Model (k + 1) → ℝ) (A : Set (Model (k + 1))),
      IsOpen A ∧ c.ambient.extend (𝓡∂ (k + 1)) x.val ∈ A ∧
      ContDiffOn ℝ ∞ β A ∧
      β =ᶠ[𝓝[(c.ambient.extend (𝓡∂ (k + 1))).target]
        (c.ambient.extend (𝓡∂ (k + 1)) x.val)]
        (fun y => φ ((c.ambient.extend (𝓡∂ (k + 1))).symm y))) :
    ∃ (a : ℝ × IntrinsicBoundary.Point k M → ℝ)
      (W : Set (ℝ × IntrinsicBoundary.Point k M)),
      IsOpen W ∧ (0, x) ∈ W ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ) ∞ a W ∧
      EqOn a (fun p => φ (C p)) (W ∩ (Ico 0 δ ×ˢ univ)) := by
  obtain ⟨g, V, ε, hg, hV, hxV, hVtarget, hε, _, hgzero, _, _, _, hmatch⟩ :=
    exists_seam_coordinate_germ_of_scalar_extensions c hx Z C hδ hzero hode hscalar hin
  obtain ⟨β, A, hA, hxA, hβ, hβeq⟩ := hφ
  let S : Set (ℝ × IntrinsicBoundary.Point k M) := univ ×ˢ c.chart.source
  let P : ℝ × IntrinsicBoundary.Point k M → ℝ × Model k :=
    fun p => (p.1, c.chart p.2)
  let G : ℝ × IntrinsicBoundary.Point k M → Model (k + 1) := g ∘ P
  let a : ℝ × IntrinsicBoundary.Point k M → ℝ := β ∘ G
  have hS : IsOpen S := isOpen_univ.prod c.chart.open_source
  have hxS : (0, x) ∈ S := ⟨mem_univ _, hx⟩
  have hc : ContMDiffOn 𝓘(ℝ, Model k) 𝓘(ℝ, Model k) ∞ c.chart c.chart.source :=
    contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas ⟨c, rfl⟩)
  have hP : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ × Model k) ∞ P S :=
    contMDiff_fst.contMDiffOn.prodMk_space
      (hc.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k))
      𝓘(ℝ, Model (k + 1)) ∞ G S := hg.contMDiff.comp_contMDiffOn hP
  have hcenter : G (0, x) = c.ambient.extend (𝓡∂ (k + 1)) x.val := by
    change g (0, c.chart x) = _
    rw [hgzero, c.toFun_eq x hx]
    apply boundaryInsert_drop
    have hex : x.val ∈ c.ambient.source := by rwa [c.source_eq] at hx
    exact (IntrinsicBoundary.isBoundaryPoint_iff_chart_zero c.mem_atlas hex).mp x.property
  have hGA : IsOpen (S ∩ G ⁻¹' A) :=
    hG.continuousOn.isOpen_inter_preimage hS hA
  have hxGA : (0, x) ∈ S ∩ G ⁻¹' A := ⟨hxS, by
    change G (0, x) ∈ A
    rwa [hcenter]⟩
  have ha : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) 𝓘(ℝ, ℝ) ∞ a
      (S ∩ G ⁻¹' A) :=
    hβ.contMDiffOn.comp (hG.mono inter_subset_left) (fun _ hp => hp.2)
  have hβeq' : ∀ᶠ z in 𝓝 (c.ambient.extend (𝓡∂ (k + 1)) x.val),
      z ∈ (c.ambient.extend (𝓡∂ (k + 1))).target →
        β z = φ ((c.ambient.extend (𝓡∂ (k + 1))).symm z) :=
    eventually_nhdsWithin_iff.mp hβeq
  have hGeq : ∀ᶠ p in 𝓝 (0, x),
      G p ∈ (c.ambient.extend (𝓡∂ (k + 1))).target →
        β (G p) = φ ((c.ambient.extend (𝓡∂ (k + 1))).symm (G p)) := by
    have hh := hG.continuousOn.continuousAt (hS.mem_nhds hxS)
    have hβeq'' : ∀ᶠ z in 𝓝 (G (0, x)),
        z ∈ (c.ambient.extend (𝓡∂ (k + 1))).target →
          β z = φ ((c.ambient.extend (𝓡∂ (k + 1))).symm z) := by
      rwa [hcenter]
    exact hh.eventually hβeq''
  obtain ⟨Q, hQeq, hQ, hxQ⟩ := mem_nhds_iff.mp hGeq
  let Y := c.chart.source ∩ c.chart ⁻¹' V
  have hY : IsOpen Y := hc.continuousOn.isOpen_inter_preimage c.chart.open_source hV
  have hxY : x ∈ Y := ⟨hx, hxV⟩
  let W := (S ∩ G ⁻¹' A) ∩ Q ∩ (Ioo (-ε) ε ×ˢ Y)
  have hW : IsOpen W := (hGA.inter hQ).inter (isOpen_Ioo.prod hY)
  have hxW : (0, x) ∈ W :=
    ⟨⟨hxGA, hxQ⟩, ⟨⟨neg_neg_of_pos hε, hε⟩, hxY⟩⟩
  refine ⟨a, W, hW, hxW, ha.mono (fun _ hp => hp.1.1), ?_⟩
  intro p hp
  have hy : p.2 ∈ Y := hp.1.2.2
  have ht : p.1 ∈ Ico 0 ε := ⟨hp.2.1.1, hp.1.2.1.2⟩
  obtain ⟨hsource, hcoord⟩ := hmatch (c.chart p.2) hy.2 p.1 ht
  rw [c.chart.left_inv hy.1] at hsource hcoord
  have hGcoord : G p = c.ambient.extend (𝓡∂ (k + 1)) (C p) := hcoord.symm
  have hGtarget : G p ∈ (c.ambient.extend (𝓡∂ (k + 1))).target := by
    rw [hGcoord]
    exact (c.ambient.extend (𝓡∂ (k + 1))).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using hsource)
  change β (G p) = φ (C p)
  rw [hQeq hp.1.1.2 hGtarget, hGcoord,
    (c.ambient.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [OpenPartialHomeomorph.extend_source] using hsource)]

end FsFltz.Geometry.IntrinsicCollar
