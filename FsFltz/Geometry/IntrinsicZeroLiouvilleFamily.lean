import FsFltz.Geometry.IntrinsicZeroLiouvilleDomain
import FsFltz.Geometry.FamilyCompletionAssembly
import FsFltz.Geometry.IntrinsicFormFamilyGluing

/-!
# Native zero-dimensional Liouville families

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, especially
lines 127–128 and 159–160; `def:chain`, lines 163–169; `sec:lean`,
lines 788–797 and 825–830. An arbitrary family of native one-forms on a
compact zero-dimensional manifold constructs a family of Liouville
structures on its own fixed compact presentation. All one-forms and fields
vanish, which proves their genuine joint smoothness. The existing collar
and completion producer then constructs actual completed families.

No completion or presentation is supplied as a hypothesis. The original
native atlas is retained, and empty manifolds are allowed. This is a
foundational family producer, not a proof of the geometric target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- The native manifold itself is the common spatial presentation; every
slice retains its supplied primitive literally. -/
abbrev liouvilleFamily (μ : Parameter → (sourceManifold M).Form 1) :
    Parameter → LiouvilleStructure (compactDomain M) :=
  fun t => (liouvilleDomain M (μ t)).liouville

omit [CompactSpace M] in
/-- Arbitrary interval-indexed native one-forms are jointly smooth in
dimension zero, with the actual zero family providing endpoint extensions. -/
theorem primitiveFamily_smooth (μ : Parameter → (sourceManifold M).Form 1) :
    (sourceManifold M).IsSmoothIntervalFormFamily μ := by
  refine ⟨fun _ => 0,
    ((sourceManifold M).isSmoothFormFamilyOn_zero univ).isSmoothFormFamily, ?_⟩
  intro t
  exact (positiveForm_eq_zero M 0 (μ t)).symm

/-- The actual constructed native Liouville fields form a jointly smooth
family, without supplying field regularity as input. -/
theorem liouvilleFamily_field_smooth (μ : Parameter → (sourceManifold M).Form 1) :
    (sourceManifold M).IsSmoothIntervalVectorFieldFamily
      (fun t => (liouvilleFamily μ t).field) := by
  refine ⟨fun _ _ => 0, ?_, ?_⟩
  · intro a
    refine ⟨univ, isOpen_univ, subset_univ _, ?_⟩
    have hz : (fun p : ℝ × Model 0 =>
        (sourceManifold M).vectorInChart a (fun _ => 0) p.2) = 0 := by
      funext p
      exact PiLp.ext (fun i => Fin.elim0 i)
    rw [hz]
    exact contDiffOn_const
  · intro t
    funext x
    exact PiLp.ext (fun i => Fin.elim0 i)

/-- Consume the general completion-family construction on the native
zero-dimensional presentation. Both collars and completed families are
constructed from the original forms. -/
def localizedCompletionFamily (μ : Parameter → (sourceManifold M).Form 1) :
    LocalizedCompletionFamily (compactDomain M) (liouvilleFamily μ) :=
  (compactDomain M).localizedCompletionFamily (liouvilleFamily μ)
    (primitiveFamily_smooth μ)

/-- The original native primitive is retained before localization. -/
@[simp] theorem liouvilleFamily_primitive
    (μ : Parameter → (sourceManifold M).Form 1) (t : Parameter) :
    (liouvilleFamily μ t).primitive = μ t := rfl

/-- The constructed complete ribbon family has stationary flow for every
real time at every required parameter. -/
theorem localizedCompletionFamily_flow
    (μ : Parameter → (sourceManifold M).Form 1) (t : Parameter) (s : ℝ)
    (x : ((localizedCompletionFamily μ).collars t).cylindricalCompletion.ambient.manifold.Point) :
    ((localizedCompletionFamily μ).collars t).cylindricalCompletion.ambient.completeFlow.flow s x = x :=
  CompleteLiouvilleManifold.flow_eq_self_of_dimension_zero _ s x

end FsFltz.Geometry.IntrinsicZeroLiouville
