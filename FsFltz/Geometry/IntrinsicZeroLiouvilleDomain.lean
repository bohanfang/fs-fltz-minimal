import FsFltz.Geometry.ZeroDimensionalCompletion
import FsFltz.Geometry.SmoothForms

/-!
# Liouville domains from arbitrary native zero-dimensional sources

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions and
`def:pair`, lines 119–160, and `sec:lean`, lines 783–814 and 825–830.
An arbitrary compact Hausdorff second-countable native smooth manifold with
zero-dimensional Euclidean charts supplies its own boundaryless extension.
Its whole carrier is compact and its boundary is empty. Every native one-form
vanishes, so smoothness, symplecticity and the zero Liouville field are proved,
rather than supplied as hypotheses. The original native atlas is retained.

The constructed domain has a native smooth carrier equivalence. Its existing
zero-dimensional completion construction then gives an actual completion and
transports the full core back to the whole original source. Empty sources are
allowed. These are general foundations, not an endpoint comparison theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable (M : Type) [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- Bundle the supplied native topology and atlas without changing them. -/
abbrev sourceManifold : SmoothManifold 0 where
  Point := M
  topology := inferInstance
  charts := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  smooth := inferInstance

omit [CompactSpace M] in
/-- Discreteness is a consequence of the original native charts. -/
theorem source_discreteTopology : DiscreteTopology M :=
  (sourceManifold M).discreteTopology_of_dimension_zero

/-- Compactness of the native zero-dimensional source implies finiteness. -/
theorem source_finite : (univ : Set M).Finite := by
  let := source_discreteTopology M
  exact isCompact_univ.finite (isDiscrete_iff_discreteTopology.mpr inferInstance)

omit [CompactSpace M] in
/-- All positive-degree forms on the native source vanish algebraically. -/
theorem positiveForm_eq_zero (r : ℕ) (α : (sourceManifold M).Form (r + 1)) :
    α = 0 := by
  funext x
  ext v
  exact (α x).map_coord_zero (0 : Fin (r + 1))
    ((sourceManifold M).tangent_eq_zero_of_dimension_zero x (v 0))

private abbrev emptyBoundary : SmoothManifold 0 := by
  letI : TopologicalSpace PEmpty := ⊥
  letI : ChartedSpace (Model 0) PEmpty := ChartedSpace.ofDiscreteTopology
  exact
    { Point := PEmpty
      topology := inferInstance
      charts := inferInstance
      hausdorff := inferInstance
      secondCountable := inferInstance
      smooth := IsManifold.of_discreteTopology ∞ }

/-- The source itself is an extension of its entire compact carrier. -/
def compactDomain : CompactDomain 0 where
  extension := sourceManifold M
  carrier := univ
  compact := isCompact_univ
  defining := fun _ hx => by simp at hx
  boundary := emptyBoundary
  boundaryInclusion :=
    { map := ⟨PEmpty.elim, by intro x; exact PEmpty.elim x⟩
      embedding := Topology.IsEmbedding.of_subsingleton _
      immersion := fun x => PEmpty.elim x }
  boundary_range := by
    ext x
    simp
  zero_boundary := fun _ => inferInstance

/-- An arbitrary original one-form determines an actual Liouville domain;
no geometric presentation or Liouville conditions are supplied as input. -/
def liouvilleDomain (α : (sourceManifold M).Form 1) : LiouvilleDomain 0 where
  domain := compactDomain M
  liouville :=
    { primitive := α
      smooth_primitive := by
        rw [positiveForm_eq_zero M 0 α]
        exact (sourceManifold M).isSmoothForm_zero
      symplectic := by
        change (sourceManifold M).IsSymplecticOn ((sourceManifold M).exteriorDerivative α) univ
        refine ⟨?_, ?_, ?_⟩
        · rw [positiveForm_eq_zero M 1 ((sourceManifold M).exteriorDerivative α)]
          exact (sourceManifold M).isSmoothForm_zero
        · intro x _
          exact congrFun (positiveForm_eq_zero M 2
            ((sourceManifold M).exteriorDerivative ((sourceManifold M).exteriorDerivative α))) x
        · intro x _
          exact (sourceManifold M).nondegenerate_zeroDimension _ x
      field := (sourceManifold M).liouvilleVector α
      smooth_field := by
        change (sourceManifold M).IsSmoothVectorField ((sourceManifold M).liouvilleVector α)
        intro a
        have hz : (sourceManifold M).vectorInChart a
            ((sourceManifold M).liouvilleVector α) = 0 := by
          funext y
          exact PiLp.ext (fun i => Fin.elim0 i)
        rw [hz]
        exact contDiffOn_const
      contraction := by
        intro x _ v
        change evalTwo ((sourceManifold M).exteriorDerivative α) x
          ((sourceManifold M).liouvilleVector α x) v = evalOne α x v
        rw [positiveForm_eq_zero M 0 α, positiveForm_eq_zero M 1
          ((sourceManifold M).exteriorDerivative 0)]
        rfl
      outward := fun _ hx => by simp [compactDomain] at hx }

variable {M}

/-- A native smooth equivalence to the actual constructed compact carrier. -/
def carrierDiffeomorph (α : (sourceManifold M).Form 1) :
    letI := (liouvilleDomain M α).domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
      (liouvilleDomain M α).domain.Point ∞ := by
  let := (liouvilleDomain M α).domain.zeroChartedSpace
  let := source_discreteTopology M
  let := (liouvilleDomain M α).domain.discreteTopology_zero
  exact
    { toEquiv :=
        { toFun := fun x => ⟨x, mem_univ x⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      contMDiff_toFun := contMDiff_of_discreteTopology
      contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem carrierDiffeomorph_val (α : (sourceManifold M).Form 1) (x : M) :
    (carrierDiffeomorph α x).val = x := rfl

/-- The native source constructs the existing geometric domain representation
with an actual smooth carrier equivalence and all form/field preservation
laws along one inclusion. The tangent derivative is bijective, and the
intrinsic and represented boundaries agree. -/
theorem exists_liouvilleDomain_with_native_presentation
    (α : (x : M) → TangentSpace 𝓘(ℝ, Model 0) x [⋀^Fin 1]→L[ℝ] ℝ) :
    ∃ (L : LiouvilleDomain 0) (i : M → L.domain.extension.Point)
      (e : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M L.domain.Point ∞),
      (∀ x, (e x).val = i x) ∧
      ContMDiff 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) i x)) ∧
      range i = L.domain.carrier ∧
      frontier L.domain.carrier = i '' (𝓘(ℝ, Model 0)).boundary M ∧
      (fun x => (L.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) i x)) = α ∧
      (fun x => (L.domain.extension.exteriorDerivative L.liouville.primitive (i x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) i x)) = (sourceManifold M).exteriorDerivative α ∧
      (∀ x, L.liouville.field (i x) =
        mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) i x
          ((sourceManifold M).liouvilleVector α x)) ∧
      L.domain.extension.IsSymplecticOn
        (L.domain.extension.exteriorDerivative L.liouville.primitive) univ := by
  refine ⟨liouvilleDomain M α, id, carrierDiffeomorph α, fun _ => rfl,
    contMDiff_id, (Homeomorph.refl M).isClosedEmbedding, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [mfderiv_id]
    exact Function.bijective_id
  · exact range_id
  · simp [liouvilleDomain, compactDomain, ModelWithCorners.Boundaryless.boundary_eq_empty]
  · exact (sourceManifold M).pullback_id α
  · exact (sourceManifold M).pullback_id ((sourceManifold M).exteriorDerivative α)
  · intro x
    rw [mfderiv_id]
    rfl
  · exact (liouvilleDomain M α).liouville.symplectic

/-- Consume the existing dimension-zero completion construction on the
domain produced directly from the native source. -/
abbrev completion (α : (sourceManifold M).Form 1) :
    Completion (liouvilleDomain M α).carrierRestriction_of_dimension_zero :=
  (liouvilleDomain M α).carrierCompletion_of_dimension_zero

/-- The actual completed ambient is natively diffeomorphic to the original
source, including when the source is empty. -/
def completionDiffeomorph (α : (sourceManifold M).Form 1) :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
      (completion α).ambient.manifold.Point ∞ := by
  let := source_discreteTopology M
  let := (completion α).ambient.manifold.discreteTopology_of_dimension_zero
  exact
    { toEquiv :=
        { toFun := fun x => ⟨x, mem_univ x⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      contMDiff_toFun := contMDiff_of_discreteTopology
      contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem completionDiffeomorph_val (α : (sourceManifold M).Form 1) (x : M) :
    (completionDiffeomorph α x).val = x := rfl

/-- The native equivalence preserves the original primitive in all tangent
directions; the completed primitive is the actual constructed one. -/
theorem completionDiffeomorph_primitive (α : (sourceManifold M).Form 1) :
    (sourceManifold M).pullback (completion α).ambient.manifold
      (completionDiffeomorph α) (completion α).ambient.primitive = α := by
  rw [(liouvilleDomain M α).carrierCompletion_primitive_of_dimension_zero,
    positiveForm_eq_zero M 0 α]
  ext x v
  rfl

/-- The same native equivalence preserves the actual exterior derivative. -/
theorem completionDiffeomorph_exteriorDerivative (α : (sourceManifold M).Form 1) :
    (sourceManifold M).pullback (completion α).ambient.manifold
      (completionDiffeomorph α)
      ((completion α).ambient.manifold.exteriorDerivative (completion α).ambient.primitive) =
        (sourceManifold M).exteriorDerivative α := by
  rw [(completion α).ambient.manifold.oneForm_eq_zero_of_dimension_zero
    ((completion α).ambient.primitive)]
  have hz : (completion α).ambient.manifold.exteriorDerivative
      (0 : (completion α).ambient.manifold.Form 1) =
        (0 : (completion α).ambient.manifold.Form 2) := by
    funext x
    ext v
    exact (((completion α).ambient.manifold.exteriorDerivative 0) x).map_coord_zero
      (0 : Fin 2) ((completion α).ambient.manifold.tangent_eq_zero_of_dimension_zero x (v 0))
  rw [hz, positiveForm_eq_zero M 1 ((sourceManifold M).exteriorDerivative α)]
  ext x v
  rfl

/-- The actual Liouville fields agree under that same equivalence. -/
theorem completionDiffeomorph_field (α : (sourceManifold M).Form 1) (x : M) :
    (completion α).ambient.field (completionDiffeomorph α x) =
      mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) (completionDiffeomorph α) x
        ((sourceManifold M).liouvilleVector α x) := by
  exact PiLp.ext (fun i => Fin.elim0 i)

/-- The full core of the actual constructed completion transports to the
entire original native source, with no completion or stationary-flow input. -/
theorem image_completion_core (α : (sourceManifold M).Form 1) :
    (Subtype.val : (completion α).ambient.manifold.Point → M) '' (completion α).core = univ :=
  (liouvilleDomain M α).image_carrierCompletion_core_of_dimension_zero

/-- Under any prescribed ribbon embedding, the transported full core has
exactly the whole ribbon image. This is the generic rank-one consumer. -/
theorem image_embedded_completion_core (α : (sourceManifold M).Form 1)
    {A : Type*} (j : M → A) :
    (j ∘ Subtype.val : (completion α).ambient.manifold.Point → A) ''
      (completion α).core = range j := by
  calc
    _ = j '' ((Subtype.val : (completion α).ambient.manifold.Point → M) ''
        (completion α).core) :=
      (image_image j (Subtype.val : (completion α).ambient.manifold.Point → M)
        (completion α).core).symm
    _ = range j := by rw [image_completion_core, image_univ]

end FsFltz.Geometry.IntrinsicZeroLiouville
