import FsFltz.Geometry.IntrinsicNativeCompactDiffeomorph
import FsFltz.Geometry.IntrinsicNativeMapFamily
import FsFltz.Geometry.IntrinsicRibbonFamily
import FsFltz.Geometry.ImmersionNeighborhood

/-!
# Native inclusion into a specified completed ambient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158, and
`sec:lean`, lines 805–814. Spatial source-chart extension germs of the
original native inclusion extend on the fixed primitive presentation.
Injectivity and full native tangent immersion give an embedding on an open
neighborhood of its whole carrier. Native primitive pullback then determines
the full primitive on that carrier, including at the boundary.

The specified target manifold and primitive are retained throughout. The raw
producer assumes neither a complete target nor a target Liouville field. This bounded producer
does not construct a completion, an equivalence onto the target, or any
target-specific marking. The native source presentation here has positive
dimension; the separate zero-dimensional adapter remains outside this result.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville
open SmoothManifold

variable {k d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- Actual spatial source-chart germs with values in the given target
manifold. Agreement is required only on the original native source. -/
def IsLocallyExtendibleTargetMap (N : SmoothManifold d) (i : M → N.Point) : Prop :=
  ∀ e : OpenPartialHomeomorph M (EuclideanHalfSpace (k + 1)),
    e ∈ atlas (EuclideanHalfSpace (k + 1)) M → ∀ x ∈ e.source,
      ∃ U : TopologicalSpace.Opens (Model (k + 1)),
        e.extend (𝓡∂ (k + 1)) x ∈ U ∧ ∃ β : U → N.Point,
          ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ β ∧
          ∀ y ∈ e.source, ∀ h : e.extend (𝓡∂ (k + 1)) y ∈ U,
            β ⟨e.extend (𝓡∂ (k + 1)) y, h⟩ = i y

/-- A spatial germ supplies the constant joint family without any new
parameter regularity assumption. -/
theorem IsLocallyExtendibleTargetMap.constantFamily
    (N : SmoothManifold d) (i : M → N.Point)
    (hi : IsLocallyExtendibleTargetMap (k := k) N i) :
    IsLocallyExtendibleMapFamily (k := k) N (fun _ : Parameter => i) := by
  intro e he t x hx
  obtain ⟨U, hxU, β, hβ, heq⟩ := hi e he x hx
  let W : TopologicalSpace.Opens (ℝ × Model (k + 1)) :=
    ⟨univ ×ˢ (U : Set (Model (k + 1))), isOpen_univ.prod U.isOpen⟩
  let a : W → U := fun p => ⟨p.val.2, p.property.2⟩
  have ha : ContMDiff 𝓘(ℝ, ℝ × Model (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ a := by
    apply (ContMDiff.subtypeVal_comp_iff U a).mp
    have h : ContMDiff 𝓘(ℝ, ℝ × Model (k + 1))
        𝓘(ℝ, Model (k + 1)) ∞ (Prod.snd : ℝ × Model (k + 1) → Model (k + 1)) :=
      (ContinuousLinearMap.snd ℝ ℝ (Model (k + 1))).contDiff.contMDiff
    exact h.comp contMDiff_subtype_val
  exact ⟨W, ⟨mem_univ _, hxU⟩, β ∘ a, hβ.comp ha,
    fun _ y hy h => heq y hy h.2⟩

private def flattenNeighborhood {r : ℕ} (F : SmoothManifold r)
    (W : TopologicalSpace.Opens F.Point) (U : TopologicalSpace.Opens W) :
    TopologicalSpace.Opens F.Point :=
  ⟨Subtype.val '' (U : Set W), W.isOpen.isOpenMap_subtype_val _ U.isOpen⟩

private def flattenDiffeomorph {r : ℕ} (F : SmoothManifold r)
    (W : TopologicalSpace.Opens F.Point) (U : TopologicalSpace.Opens W) :
    (F.restrict (flattenNeighborhood F W U)).SmoothEquiv ((F.restrict W).restrict U) := by
  let V := flattenNeighborhood F W U
  let f : V → U := fun x =>
    ⟨⟨x.val, by obtain ⟨y, _, he⟩ := x.property; exact he ▸ y.property⟩, by
      obtain ⟨y, hy, he⟩ := x.property
      exact (show y = (⟨x.val, _⟩ : W) from Subtype.ext he) ▸ hy⟩
  let g : U → V := fun y => ⟨y.val.val, ⟨y.val, y.property, rfl⟩⟩
  have hf : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, Model r) ∞ f := by
    apply (ContMDiff.subtypeVal_comp_iff U f).mp
    apply (ContMDiff.subtypeVal_comp_iff W (Subtype.val ∘ f)).mp
    exact contMDiff_subtype_val
  have hg : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, Model r) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff V g).mp
    change ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, Model r) ∞
      ((Subtype.val : W → F.Point) ∘ (Subtype.val : U → W))
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  exact
    { toFun := f
      invFun := g
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      contMDiff_toFun := hf
      contMDiff_invFun := hg }

variable [CompactSpace M]

namespace NativeLiouvillePresentation

/-- Original source-local inclusion germs, injectivity, full tangent
immersion, and native primitive pullback construct an actual embedding near
the fixed presentation's carrier into the same specified smooth ambient.
Both the differentiated square and primitive equality use all tangent
directions. No ambient extension embedding or completion is assumed. -/
theorem exists_inclusionEmbedding_into_specified_manifold
    {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (N : SmoothManifold d) (lam : N.Form 1) (i : M → N.Point)
    (hi : IsLocallyExtendibleTargetMap (k := k) N i)
    (hinj : Function.Injective i)
    (himm : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x))
    (hpull : ∀ x, (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x) = α x) :
    ∃ (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (hU : P.domain.domain.carrier ⊆ U)
      (J : (P.domain.domain.extension.restrict U).SmoothEmbedding N),
      (∀ x, J.map ((P.restrict U hU).inclusion x) = i x) ∧
      (∀ x,
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) J.map
          ((P.restrict U hU).inclusion x)).comp
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (P.restrict U hU).inclusion x) =
          mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x) ∧
      ∀ z ∈ (P.domain.restrict U hU).domain.carrier,
        (P.domain.domain.extension.restrict U).pullback N J.map lam z =
          (P.domain.restrict U hU).liouville.primitive z := by
  obtain ⟨W, hW, g, hg, heq⟩ := exists_mapFamily_on_fixed_presentation
    P.domain.domain.extension P.inclusion P.embedding P.coordinates N
      (fun _ : Parameter => i) (hi.constantFamily N i)
  have hcover : parameterInterval ×ˢ P.domain.domain.carrier ⊆ W := by
    rwa [← P.carrier_range]
  obtain ⟨V, T, hV, hT, hrect, f, hfval, hfs⟩ :=
    P.domain.domain.extension.exists_partialFamily_rectangle N
      P.domain.domain.carrier P.domain.domain.compact W hcover g hg
  let P₀ := P.restrict V hV
  have hf : ContMDiff 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) ∞ (f 0) := by
    intro z
    exact ((hfs.contMDiffAt ((T.isOpen.prod isOpen_univ).mem_nhds
      (show (0, z) ∈ (T : Set ℝ) ×ˢ univ from
        ⟨hT parameterZero.property, mem_univ _⟩))).comp z
          (contMDiffAt_const.prodMk contMDiffAt_id))
  have hsquare (x : M) : f 0 (P₀.inclusion x) = i x :=
    (hfval 0 (hT parameterZero.property) (P₀.inclusion x)).trans
      (heq parameterZero x _)
  have hfimm : ∀ z ∈ P₀.domain.domain.carrier, Function.Injective
      (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) (f 0) z) := by
    intro z hz
    rw [← P₀.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact injective_mfderiv_of_native_comp_on_presentation P₀.domain.domain.extension
      N P₀.inclusion P₀.smooth_inclusion (fun x => (P₀.tangent_bijective x).2)
      (f 0) hf i hsquare himm x
  have hfinj : InjOn (f 0) P₀.domain.domain.carrier := by
    intro y hy z hz h
    rw [← P₀.carrier_range] at hy hz
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact congrArg P₀.inclusion (hinj ((hsquare a).symm.trans (h.trans (hsquare b))))
  obtain ⟨U₀, hU₀, j, _, hj⟩ :=
    P₀.domain.domain.extension.exists_smooth_embedding_neighborhood N
      P₀.domain.domain.carrier P₀.domain.domain.compact (f 0) univ isOpen_univ
      (fun _ _ => mem_univ _) hf.contMDiffOn hfinj hfimm
  change TopologicalSpace.Opens V at U₀
  change ((P.domain.domain.extension.restrict V).restrict U₀).SmoothEmbedding N at j
  change ∀ x : U₀, j.map x = f 0 x.val at hj
  change (Subtype.val : V → P.domain.domain.extension.Point) ⁻¹'
    P.domain.domain.carrier ⊆ (U₀ : Set V) at hU₀
  let U := flattenNeighborhood P.domain.domain.extension V U₀
  have hU : P.domain.domain.carrier ⊆ U := by
    intro z hz
    exact ⟨⟨z, hV hz⟩, hU₀ hz, rfl⟩
  let a := flattenDiffeomorph P.domain.domain.extension V U₀
  let J : (P.domain.domain.extension.restrict U).SmoothEmbedding N :=
    { map := ⟨j.map ∘ a, j.map.contMDiff.comp a.contMDiff⟩
      embedding := j.embedding.comp a.toHomeomorph.isEmbedding
      immersion := by
        intro z
        change Function.Injective (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d)
          (j.map ∘ a) z)
        rw [mfderiv_comp z (j.map.contMDiff.mdifferentiableAt (by simp))
          (a.contMDiff.mdifferentiableAt (by simp))]
        exact (j.immersion (a z)).comp (a.isInvertible_mfderiv (by simp)).injective }
  let P₁ := P.restrict U hU
  have hJ (x : M) : J.map (P₁.inclusion x) = i x := by
    change j.map (a (P₁.inclusion x)) = _
    rw [hj]
    have ha : (a (P₁.inclusion x)).val = P₀.inclusion x := Subtype.ext rfl
    rw [ha]
    exact hsquare x
  refine ⟨U, hU, J, hJ, ?_, ?_⟩
  · intro x
    have hd := mfderiv_comp (f := P₁.inclusion) (g := J.map) x
      (J.map.contMDiff.mdifferentiableAt (by simp))
      (P₁.smooth_inclusion.mdifferentiableAt (by simp))
    rw [show J.map ∘ P₁.inclusion = i from funext hJ] at hd
    exact hd.symm
  · intro z hz
    change z ∈ P₁.domain.domain.carrier at hz
    rw [← P₁.carrier_range] at hz
    obtain ⟨x, rfl⟩ := hz
    exact pullback_eq_of_native_comp_on_presentation P₁.domain.domain.extension
      N P₁.inclusion P₁.smooth_inclusion (fun x => (P₁.tangent_bijective x).2)
      J.map J.map.contMDiff i hJ lam P₁.domain.liouville.primitive α
      (fun x => congrFun P₁.primitive x) hpull x


/-- Compatibility adapter for an already complete ambient. The construction
itself depends only on its smooth manifold and primitive. -/
theorem exists_inclusionEmbedding_into_specified_ambient
    {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (X : CompleteLiouvilleManifold d) (i : M → X.manifold.Point)
    (hi : IsLocallyExtendibleTargetMap (k := k) X.manifold i)
    (hinj : Function.Injective i)
    (himm : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x))
    (hpull : ∀ x, (X.primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x) = α x) :
    ∃ (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (hU : P.domain.domain.carrier ⊆ U)
      (J : (P.domain.domain.extension.restrict U).SmoothEmbedding X.manifold),
      (∀ x, J.map ((P.restrict U hU).inclusion x) = i x) ∧
      (∀ x,
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model d) J.map
          ((P.restrict U hU).inclusion x)).comp
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (P.restrict U hU).inclusion x) =
          mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) i x) ∧
      ∀ z ∈ (P.domain.restrict U hU).domain.carrier,
        (P.domain.domain.extension.restrict U).pullback X.manifold J.map X.primitive z =
          (P.domain.restrict U hU).liouville.primitive z := by
  exact P.exists_inclusionEmbedding_into_specified_manifold X.manifold X.primitive i
    hi hinj himm hpull

end NativeLiouvillePresentation
end FsFltz.Geometry.IntrinsicLiouville
