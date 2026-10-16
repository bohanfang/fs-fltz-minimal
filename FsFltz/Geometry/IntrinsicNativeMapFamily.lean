import FsFltz.Geometry.IntrinsicLiouvilleFamilyExtension
import FsFltz.Geometry.IntrinsicMapExtension
import FsFltz.Geometry.PartialPairGermFamilyConstruction

/-!
# Joint native map germs on the primitive family's fixed presentation

Source: `geoemtric-part-fsf.tex`, conventions 119–122, `def:pair`,
132–146, `def:chain`, 163–169, and `sec:lean`, 788–814.
Actual joint local map germs, including the parameter endpoints and native
spatial boundary, glue to one partial family near the whole compact product.
The coordinate extensions are the ones constructed with the primitive family;
no globally extended map family or agreement off the native carrier is input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Genuine local joint manifold-valued extension germs in native source
charts. Each germ takes values in the target manifold itself; its open domain
extends across both the native spatial boundary and parameter endpoints. -/
def IsLocallyExtendibleMapFamily (N : SmoothManifold d)
    (f : Parameter → M → N.Point) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ t : Parameter, ∀ x ∈ e.source,
      ∃ U : TopologicalSpace.Opens (ℝ × Model (k + 1)),
        (t.val, e.extend (𝓡∂ (k + 1)) x) ∈ U ∧ ∃ β : U → N.Point,
          ContMDiff 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model d) ∞ β ∧
          ∀ s : Parameter, ∀ y ∈ e.source, ∀ h : (s.val, e.extend (𝓡∂ (k + 1)) y) ∈ U,
            β ⟨(s.val, e.extend (𝓡∂ (k + 1)) y), h⟩ = f s y

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Transport and finite target-chart gluing of native joint map germs on
one fixed native compact presentation. Only the actual local coordinate
extensions of that same presentation are used. Empty native carriers and
empty targets require no inhabitedness hypothesis. -/
theorem exists_mapFamily_on_fixed_presentation {r : ℕ}
    [CompactSpace M]
    (F : SmoothManifold r) (i : M → F.Point)
    (hemb : Topology.IsClosedEmbedding i)
    (hcoord : HasNativeCoordinateExtensions (k := k) F i)
    (N : SmoothManifold d) (f : Parameter → M → N.Point)
    (hf : IsLocallyExtendibleMapFamily (k := k) N f) :
    ∃ W : TopologicalSpace.Opens (ℝ × F.Point),
      parameterInterval ×ˢ range i ⊆ W ∧ ∃ g : W → N.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) 𝓘(ℝ, Model d) ∞ g ∧
        ∀ t x (h : (t.val, i x) ∈ W), g ⟨(t.val, i x), h⟩ = f t x := by
  classical
  have hprod : IsManifold ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) ∞
      (ℝ × F.Point) := inferInstance
  let : ChartedSpace (ℝ × Model r) (ℝ × F.Point) :=
    prodChartedSpace ℝ ℝ (Model r) F.Point
  rw [← modelWithCornersSelf_prod] at hprod
  let : IsManifold 𝓘(ℝ, ℝ × Model r) ∞ (ℝ × F.Point) := hprod
  let A := parameterInterval ×ˢ range i
  let f₀ : A → N.Point := fun p => f ⟨p.val.1, p.property.1⟩ p.property.2.choose
  have hfi (t : Parameter) (x : M) (h : (t.val, i x) ∈ A) :
      f₀ ⟨(t.val, i x), h⟩ = f t x := by
    exact congrArg (f t) (hemb.injective h.2.choose_spec)
  have hlocal : ∀ p : A, ∃ O : TopologicalSpace.Opens (ℝ × F.Point), p.val ∈ O ∧
      ∃ g : O → N.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) 𝓘(ℝ, Model d) ∞ g ∧
        ∀ q (hqO : q ∈ O) (hqA : q ∈ A), g ⟨q, hqO⟩ = f₀ ⟨q, hqA⟩ := by
    rintro ⟨⟨s, z⟩, hp⟩
    obtain ⟨hs, x, hx⟩ := hp
    dsimp only at hx
    subst z
    let t : Parameter := ⟨s, hs⟩
    obtain ⟨e, V, Q, he, hV, hxV, hQ, hagree⟩ := hcoord x
    obtain ⟨U, hpU, β, hβ, hβeq⟩ := hf e he t x (hagree x hxV).1
    let P : ℝ × F.Point → ℝ × Model (k + 1) := fun p => (p.1, Q p.2)
    let O : TopologicalSpace.Opens (ℝ × F.Point) :=
      ⟨(univ ×ˢ V) ∩ P ⁻¹' U,
        (contMDiff_fst.contMDiffOn.prodMk_space
          (hQ.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))).continuousOn.isOpen_inter_preimage
            (isOpen_univ.prod hV) U.isOpen⟩
    let a : O → U := fun p => ⟨P p.val, p.property.2⟩
    have hP : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r))
        𝓘(ℝ, ℝ × Model (k + 1)) ∞ P (univ ×ˢ V) :=
      contMDiff_fst.contMDiffOn.prodMk_space
        (hQ.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
    have ha : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r))
        𝓘(ℝ, ℝ × Model (k + 1)) ∞ a := by
      apply (ContMDiff.subtypeVal_comp_iff U a).mp
      intro p
      exact ((hP.contMDiffAt ((isOpen_univ.prod hV).mem_nhds p.property.1)).comp
        p contMDiff_subtype_val.contMDiffAt)
    have hpO : (s, i x) ∈ O := ⟨⟨mem_univ _, hxV⟩, by
      change (s, Q (i x)) ∈ U
      rw [(hagree x hxV).2]
      exact hpU⟩
    refine ⟨O, hpO, β ∘ a, hβ.comp ha, ?_⟩
    intro q hqO hqA
    rcases q with ⟨s', z'⟩
    obtain ⟨hs', y, hy⟩ := hqA
    dsimp only at hy
    subst z'
    let t' : Parameter := ⟨s', hs'⟩
    obtain ⟨hysource, hyQ⟩ := hagree y hqO.1.2
    have hyU : (s', e.extend (𝓡∂ (k + 1)) y) ∈ U := by
      have h := hqO.2
      change (s', Q (i y)) ∈ U at h
      rwa [hyQ] at h
    have heq : (β ∘ a) ⟨(s', i y), hqO⟩ = f t' y := by
      change β ⟨(s', Q (i y)), hqO.2⟩ = _
      have harg : (⟨(s', Q (i y)), hqO.2⟩ : U) =
          ⟨(s', e.extend (𝓡∂ (k + 1)) y), hyU⟩ := Subtype.ext (Prod.ext rfl hyQ)
      exact (congrArg β harg).trans (hβeq t' y hysource hyU)
    exact heq.trans (hfi t' y ⟨hs', mem_range_self y⟩).symm
  have hcompact : IsCompact A := isCompact_Icc.prod
    (by simpa only [image_univ] using isCompact_univ.image hemb.continuous)
  simp_rw +instances [← modelWithCornersSelf_prod] at hlocal
  obtain ⟨W, hW, g, hg, heq⟩ :=
    SmoothMapExtension.exists_smoothMapExtension_of_compact hcompact f₀ hlocal
  rw [modelWithCornersSelf_prod] at hg
  exact ⟨W, hW, g, hg, fun t x h =>
    (heq (t.val, i x) h ⟨t.property, mem_range_self x⟩).trans
      (hfi t x ⟨t.property, mem_range_self x⟩)⟩

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- A partial family that agrees on the native carrier is smooth on every
native time slice. This is a consequence of the joint extension, rather than
a separately assumed slice regularity certificate. -/
theorem contMDiff_native_slice_of_partialFamily {r : ℕ}
    (F : SmoothManifold r) (i : M → F.Point)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) ∞ i)
    (N : SmoothManifold d) (f : Parameter → M → N.Point)
    (W : TopologicalSpace.Opens (ℝ × F.Point))
    (hcover : parameterInterval ×ˢ range i ⊆ W) (g : W → N.Point)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) 𝓘(ℝ, Model d) ∞ g)
    (heq : ∀ t x (h : (t.val, i x) ∈ W), g ⟨(t.val, i x), h⟩ = f t x)
    (t : Parameter) : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) ∞ (f t) := by
  let a : M → W := fun x => ⟨(t.val, i x), hcover ⟨t.property, mem_range_self x⟩⟩
  have ha : ContMDiff (𝓡∂ (k + 1))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model r)) ∞ a :=
    (ContMDiff.subtypeVal_comp_iff W a).mp (contMDiff_const.prodMk hi)
  have hfun : g ∘ a = f t := funext (fun x => heq t x _)
  rw [← hfun]
  exact hg.comp ha

end FsFltz.Geometry.IntrinsicLiouville
