import FsFltz.Geometry.IntrinsicZeroCompactDiffeomorph

/-!
# Zero-dimensional completions on the original native ambient

Source: `geoemtric-part-fsf.tex`, differential-geometric conventions,
lines 119–128; `def:pair`, lines 142–160; `sec:lean`, lines 783–814
and 825–830. The compact native zero-dimensional source itself is a
complete ambient: its original primitive and Liouville field vanish,
and its complete flow is stationary for every real time. Its completion
has identity inclusion and no cylindrical end.

Unlike the carrier-restriction realization, this construction retains the
original native type, topology and atlas literally as the completed ambient.
A primitive-preserving inclusion marking relates the existing native
completion to this ambient. Empty sources are allowed, and no completion,
stationary-flow or nonemptiness hypothesis is supplied. This is a general
foundation, not a full-fiber marking or geometric endpoint theorem.
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

/-- The original native zero-dimensional source has an explicit stationary
all-real-time flow solving its original Liouville field's coordinate ODE. -/
def sourceCompleteFlow (α : (sourceManifold M).Form 1) :
    CompleteLiouvilleFlow (sourceManifold M) (liouvilleDomain M α).liouville.field where
  flow := Flow.id ℝ M
  smooth_action := contMDiff_snd
  solves := by
    intro x t a _
    change HasDerivAt (fun _ : ℝ => chartAt (Model 0) a x)
      ((sourceManifold M).chartTangentMap a x ((liouvilleDomain M α).liouville.field x)) t
    have hz : (sourceManifold M).chartTangentMap a x
        ((liouvilleDomain M α).liouville.field x) = 0 :=
      PiLp.ext (fun i => Fin.elim0 i)
    rw [hz]
    exact hasDerivAt_const t (chartAt (Model 0) a x)

/-- A complete Liouville ambient on the literal original native carrier,
with its original one-form and Liouville field. -/
def sourceCompleteManifold (α : (sourceManifold M).Form 1) : CompleteLiouvilleManifold 0 where
  manifold := sourceManifold M
  primitive := α
  smooth_primitive := (liouvilleDomain M α).liouville.smooth_primitive
  symplectic := (liouvilleDomain M α).liouville.symplectic
  field := (liouvilleDomain M α).liouville.field
  smooth_field := (liouvilleDomain M α).liouville.smooth_field
  contraction := fun x => (liouvilleDomain M α).liouville.contraction x (mem_univ x)
  completeFlow := sourceCompleteFlow α

/-- Completion of the original whole native compact domain on the native
source itself. Its inclusion is identity and its cylindrical end is empty. -/
def sourceCompletion (α : (sourceManifold M).Form 1) : Completion (liouvilleDomain M α) := by
  letI : IsEmpty (liouvilleDomain M α).domain.boundary.Point :=
    (liouvilleDomain M α).domain.zero_boundary rfl
  exact
    { ambient := sourceCompleteManifold α
      inclusion :=
        { map := ContMDiffMap.id
          embedding := Topology.IsEmbedding.id
          immersion := fun x => by
            change Function.Injective (mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) id x)
            rw [mfderiv_id]
            exact Function.injective_id }
      primitive_on_domain := fun x _ => congrFun ((sourceManifold M).pullback_id α) x
      field_on_domain := fun x _ => by
        change mfderiv 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) id x
          ((liouvilleDomain M α).liouville.field x) = _
        rw [mfderiv_id]
        rfl
      endMap := fun p => isEmptyElim p.1
      smooth_endMap := contMDiff_of_discreteTopology
      end_flow := fun x => isEmptyElim x
      end_embedding := Topology.IsEmbedding.of_subsingleton _
      end_immersion := fun p => isEmptyElim p.1
      end_primitive := fun x => isEmptyElim x
      covering := by
        apply eq_univ_of_forall
        intro x
        exact Or.inl ⟨x, mem_univ x, rfl⟩
      overlap := fun x => isEmptyElim x }

@[simp] theorem sourceCompletion_inclusion (α : (sourceManifold M).Form 1) (x : M) :
    (sourceCompletion α).inclusion.map x = x := rfl

/-- The original native primitive, retained by the complete ambient, is zero. -/
@[simp] theorem sourceCompletion_primitive (α : (sourceManifold M).Form 1) :
    (sourceCompletion α).ambient.primitive = 0 := positiveForm_eq_zero M 0 α

@[simp] theorem sourceCompletion_field (α : (sourceManifold M).Form 1) (x : M) :
    (sourceCompletion α).ambient.field x = (0 : Model 0) :=
  (sourceManifold M).tangent_eq_zero_of_dimension_zero x _

/-- The constructed native flow is stationary in both time directions. -/
@[simp] theorem sourceCompletion_flow (α : (sourceManifold M).Form 1) (t : ℝ) (x : M) :
    (sourceCompletion α).ambient.completeFlow.flow t x = x := rfl

/-- The completion's full intrinsic core is literally the original source. -/
@[simp] theorem sourceCompletion_core (α : (sourceManifold M).Form 1) :
    (sourceCompletion α).core = univ := by
  rw [Completion.core_eq_carrier_of_dimension_zero]
  rfl

/-- Every prescribed native ribbon map carries this full core to its entire
original image, with no change of the native point type. -/
theorem image_sourceCompletion_core (α : (sourceManifold M).Form 1)
    {A : Type*} (j : M → A) : j '' (sourceCompletion α).core = range j := by
  rw [sourceCompletion_core, image_univ]

/-- The existing subtype realization is marked onto the literal native
complete ambient. The marking retains the original compact inclusion and
is primitive preserving and induced by the same stationary Liouville flow. -/
def nativeCompletionSourceMarking (α : (sourceManifold M).Form 1) :
    InclusionMarking (nativeCompletion α) (sourceCompleteManifold α)
      (Subtype.val : (liouvilleDomain M α).domain.Point → M) := by
  letI : IsEmpty (liouvilleDomain M α).domain.boundary.Point :=
    (liouvilleDomain M α).domain.zero_boundary rfl
  exact
    { equiv := (completionDiffeomorph α).symm
      primitive := by
        exact ((nativeCompletion α).ambient.manifold.oneForm_eq_zero_of_dimension_zero
          _).trans ((nativeCompletion α).ambient.manifold.oneForm_eq_zero_of_dimension_zero
            _).symm
      inclusion := fun _ => rfl
      flow_induced := fun x => isEmptyElim x }

@[simp] theorem nativeCompletionSourceMarking_native
    (α : (sourceManifold M).Form 1) (x : M) :
    (nativeCompletionSourceMarking α).equiv ((nativeCompletion α).inclusion.map x) = x := rfl

end FsFltz.Geometry.IntrinsicZeroLiouville
