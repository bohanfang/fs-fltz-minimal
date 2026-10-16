import FsFltz.Geometry.IntrinsicBundlePrimitiveData
import FsFltz.Geometry.IntrinsicNativeCompactDiffeomorph

/-!
# Native extension germs from the original bundle transition germs

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:chain`,
lines 163–169, and `sec:lean`, lines 788–814. Self transitions extend
identity coordinate changes across the native boundary. Their full
derivatives are invertible, so local inversion changes the preferred target
chart in an original transition germ to any requested original spatial
chart. No strengthened transition regularity assumption is needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The full differential of a native chart is invertible, including
at a spatial boundary point. -/
private theorem nativeChartTangent_bijective
    (a : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (ha : a ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (x : M) (hx : x ∈ a.source) : Function.Bijective (chartTangentMap a x) := by
  constructor
  · intro v w h
    exact (inverseChartTangentMap_chartTangentMap ha hx v).symm.trans
      ((congrArg (inverseChartTangentMap a (a.extend (𝓡∂ (k + 1)) x)) h).trans
        (inverseChartTangentMap_chartTangentMap ha hx w))
  · intro v
    have hxt : a.extend (𝓡∂ (k + 1)) x ∈ (a.extend (𝓡∂ (k + 1))).target :=
      (a.extend (𝓡∂ (k + 1))).map_source (by simpa only [a.extend_source] using hx)
    refine ⟨inverseChartTangentMap a (a.extend (𝓡∂ (k + 1)) x) v, ?_⟩
    have h := chartTangentMap_inverseChartTangentMap ha hxt v
    rwa [(a.extend (𝓡∂ (k + 1))).left_inv
      (by simpa only [a.extend_source] using hx)] at h

/-- An open extension of identity between two native coordinates has
invertible full ambient derivative. Its native agreement determines the
derivative through the two invertible native chart tangent maps. -/
private theorem identityCoordinateExtension_bijective
    (a b : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (ha : a ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (hb : b ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (x : M) (hx : x ∈ a.source) (hxb : x ∈ b.source)
    (U : Set (Model (k + 1))) (hU : IsOpen U)
    (β : Model (k + 1) → Model (k + 1))
    (hβ : ContDiffOn ℝ ∞ β U) (hxU : a.extend (𝓡∂ (k + 1)) x ∈ U)
    (heq : ∀ y ∈ a.source, a.extend (𝓡∂ (k + 1)) y ∈ U →
      β (a.extend (𝓡∂ (k + 1)) y) = b.extend (𝓡∂ (k + 1)) y) :
    Function.Bijective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) β
      (a.extend (𝓡∂ (k + 1)) x)) := by
  have haS := a.contMDiffOn_extend (I := 𝓡∂ (k + 1))
    (IsManifold.subset_maximalAtlas (n := ∞) ha)
  have haA := haS.contMDiffAt (a.open_source.mem_nhds hx)
  have hag : β ∘ a.extend (𝓡∂ (k + 1)) =ᶠ[𝓝 x] b.extend (𝓡∂ (k + 1)) := by
    filter_upwards [a.open_source.mem_nhds hx,
      haA.continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
    exact heq y hy hyU
  have hd := mfderiv_comp x
    ((hβ.contDiffAt (hU.mem_nhds hxU)).contMDiffAt.mdifferentiableAt (by simp))
    (haA.mdifferentiableAt (by simp))
  have hs : (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) β
      (a.extend (𝓡∂ (k + 1)) x)).comp (chartTangentMap a x) = chartTangentMap b x :=
    hd.symm.trans hag.mfderiv_eq
  constructor
  · intro v w h
    obtain ⟨v', rfl⟩ := (nativeChartTangent_bijective a ha x hx).2 v
    obtain ⟨w', rfl⟩ := (nativeChartTangent_bijective a ha x hx).2 w
    apply congrArg (chartTangentMap a x)
    apply (nativeChartTangent_bijective b hb x hxb).1
    exact (congrArg (fun T => T v') hs).symm.trans
      (h.trans (congrArg (fun T => T w') hs))
  · intro v
    obtain ⟨v', hv⟩ := (nativeChartTangent_bijective b hb x hxb).2 v
    exact ⟨chartTangentMap a x v', (congrArg (fun T => T v') hs).trans hv⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Freeze one joint chosen-target coordinate germ without losing its
open across-boundary extension. -/
private theorem HasSmoothFamilyOn.coordinate_germ {S : Set Parameter}
    {f : Parameter → M → M} (h : HasSmoothFamilyOn (𝓡∂ (k + 1)) S f)
    (a : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)))
    (ha : a ∈ atlas (EuclideanHalfSpace (k + 1)) M)
    (t : Parameter) (ht : t ∈ S) (x : M) (hx : x ∈ a.source) :
    ∃ (U : Set (Model (k + 1))) (β : Model (k + 1) → Model (k + 1)),
      IsOpen U ∧ a.extend (𝓡∂ (k + 1)) x ∈ U ∧ ContDiffOn ℝ ∞ β U ∧
      ∀ y ∈ a.source, a.extend (𝓡∂ (k + 1)) y ∈ U →
        β (a.extend (𝓡∂ (k + 1)) y) = extChartAt (𝓡∂ (k + 1)) (f t x) (f t y) := by
  obtain ⟨V, γ, hV, hxV, hγ, heq⟩ := h a ha t ht x hx
  let q : Model (k + 1) → ℝ × Model (k + 1) := fun z => (t.val, z)
  have hq : ContDiff ℝ ∞ q := contDiff_const.prodMk contDiff_id
  refine ⟨q ⁻¹' V, γ ∘ q, hV.preimage hq.continuous, hxV,
    hγ.comp hq.contDiffOn (fun _ hz => hz), ?_⟩
  intro y hy hyV
  have hyT : a.extend (𝓡∂ (k + 1)) y ∈ (a.extend (𝓡∂ (k + 1))).target :=
    (a.extend (𝓡∂ (k + 1))).map_source (by simpa only [a.extend_source] using hy)
  simpa only [Function.comp_apply, q,
    (a.extend (𝓡∂ (k + 1))).left_inv (by simpa only [a.extend_source] using hy)] using
      heq t ht _ hyT hyV

/-- Original chosen-target joint germs, together with the original self
transition germs, imply arbitrary-target native spatial extensions. Local
inversion of the identity germ changes target coordinates. -/
theorem HasSmoothFamilyOn.native_slice_of_identity_germs
    {S : Set Parameter} {f : Parameter → M → M}
    (hf : HasSmoothFamilyOn (𝓡∂ (k + 1)) S f)
    (hi : HasSmoothFamilyOn (𝓡∂ (k + 1)) S (fun _ => (id : M → M)))
    (t : Parameter) (ht : t ∈ S) (hfc : Continuous (f t)) :
    IsLocallyExtendibleNativeMap (k := k) (f t) := by
  intro a ha x hx b hb hxb
  let y := f t x
  let c := chartAt (EuclideanHalfSpace (k + 1)) y
  obtain ⟨U, β, hU, hyU, hβ, heβ⟩ := hi.coordinate_germ b hb t ht y hxb
  have hβeq : ∀ z ∈ b.source, b.extend (𝓡∂ (k + 1)) z ∈ U →
      β (b.extend (𝓡∂ (k + 1)) z) = c.extend (𝓡∂ (k + 1)) z := by
    intro z hz hzU
    exact heβ z hz hzU
  have hbij := identityCoordinateExtension_bijective b c hb (chart_mem_atlas _ y)
    y hxb (mem_chart_source _ y) U hU β hβ hyU hβeq
  obtain ⟨q, hyq, hq⟩ := isLocalDiffeomorphAt_of_bijective_mfderiv_manifold
    hU hβ.contMDiffOn hyU hbij
  obtain ⟨V, γ, hV, hxV, hγ, heγ⟩ := hf.coordinate_germ a ha t ht x hx
  let z₀ := a.extend (𝓡∂ (k + 1)) x
  let u : Model (k + 1) → M := (a.extend (𝓡∂ (k + 1))).symm
  have hu : ContinuousAt u z₀ := a.continuousAt_extend_symm (I := 𝓡∂ (k + 1)) hx
  have hux : u z₀ = x := (a.extend (𝓡∂ (k + 1))).left_inv
    (by simpa only [a.extend_source] using hx)
  have hfu : ContinuousAt (f t ∘ u) z₀ := hfc.continuousAt.comp_of_eq hu hux
  have hbu : ContinuousAt (b.extend (𝓡∂ (k + 1)) ∘ f t ∘ u) z₀ :=
    (b.continuousAt_extend (I := 𝓡∂ (k + 1)) hxb).comp_of_eq hfu
      (by simp only [Function.comp_apply, hux])
  have hWnhds : {z | f t (u z) ∈ b.source ∧
      b.extend (𝓡∂ (k + 1)) (f t (u z)) ∈ U ∩ q.source} ∈ 𝓝 z₀ := by
    exact inter_mem (hfu.preimage_mem_nhds (b.open_source.mem_nhds
      (by simpa only [Function.comp_apply, hux] using hxb)))
      (hbu.preimage_mem_nhds ((hU.inter q.open_source).mem_nhds
        (by simpa only [Function.comp_apply, hux, y, mem_inter_iff] using And.intro hyU hyq)))
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hWnhds
  have hγx : γ z₀ = q (b.extend (𝓡∂ (k + 1)) y) :=
    (heγ x hx hxV).trans ((hβeq y hxb hyU).symm.trans (hq hyq))
  let O : Set (Model (k + 1)) := (V ∩ W) ∩ γ ⁻¹' q.target
  have hO : IsOpen O :=
    (hγ.mono inter_subset_left).continuousOn.isOpen_inter_preimage
      (hV.inter hW) q.open_target
  have hxO : z₀ ∈ O := ⟨⟨hxV, hxW⟩, by
    change γ z₀ ∈ q.target
    rw [hγx]
    exact q.map_source hyq⟩
  refine ⟨O, q.invFun ∘ γ, hO, hxO, ?_, ?_⟩
  · have hh := q.contMDiffOn_invFun.comp
        (hγ.mono (fun _ (hz : _ ∈ O) => hz.1.1)).contMDiffOn
        (fun z (hz : z ∈ O) => hz.2)
    exact hh.contDiffOn
  · intro z hz hzO
    have huz : u (a.extend (𝓡∂ (k + 1)) z) = z :=
      (a.extend (𝓡∂ (k + 1))).left_inv (by simpa only [a.extend_source] using hz)
    have hzW := hWsub hzO.1.2
    change f t (u (a.extend (𝓡∂ (k + 1)) z)) ∈ b.source ∧
      b.extend (𝓡∂ (k + 1)) (f t (u (a.extend (𝓡∂ (k + 1)) z))) ∈ U ∩ q.source at hzW
    rw [huz] at hzW
    change q.invFun (γ (a.extend (𝓡∂ (k + 1)) z)) = _
    rw [heγ z hz hzO.1.1]
    change q.invFun (c.extend (𝓡∂ (k + 1)) (f t z)) = _
    rw [← hβeq (f t z) hzW.1 hzW.2.1, hq hzW.2.2]
    exact q.left_inv hzW.2.2

variable {E : Parameter → Type*} [∀ t, TopologicalSpace (E t)]
  [TopologicalSpace (TotalSpace M E)]

omit [∀ t, TopologicalSpace (E t)] in
/-- Freeze an actual ordered compact-bundle transition and use the
actual target-chart self transition to derive arbitrary-target extensions.
Both kinds of germ are part of the original smooth bundle atlas. -/
theorem HasSmoothTransition.native_slice
    {e e' : Trivialization M (π M E)}
    (h : HasSmoothTransition (𝓡∂ (k + 1)) e e')
    (hi : HasSmoothTransition (𝓡∂ (k + 1)) e' e')
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    IsLocallyExtendibleNativeMap (k := k) (e.coordChange e' t) := by
  have hid : HasSmoothFamilyOn (𝓡∂ (k + 1)) (e.baseSet ∩ e'.baseSet)
      (fun _ => (id : M → M)) :=
    (hi.hasSmoothFamilyOn.mono (fun _ hs => ⟨hs.2, hs.2⟩)).congr
      (fun s hs x => by simp only [e'.coordChange_same hs.2, id_eq])
  exact h.hasSmoothFamilyOn.native_slice_of_identity_germs hid t ht
    (e.continuous_coordChange e' ht.1 ht.2)

variable [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]

/-- The original smooth compact bundle supplies every needed spatial
transition extension. No additional native or completed regularity field
is introduced into the source bundle. -/
theorem isLocallyExtendibleNativeMap_coordChange
    (e e' : Trivialization M (π M E))
    (he : e ∈ trivializationAtlas M E) (he' : e' ∈ trivializationAtlas M E)
    {t : Parameter} (ht : t ∈ e.baseSet ∩ e'.baseSet) :
    IsLocallyExtendibleNativeMap (k := k) (e.coordChange e' t) :=
  (SmoothCompactBundle.smoothTransition e he e' he').native_slice
    (SmoothCompactBundle.smoothTransition e' he' e' he') ht

end FsFltz.Geometry.IntrinsicSmoothBundle
