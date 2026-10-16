import FsFltz.Geometry.IntrinsicZeroLiouvilleFamily
import FsFltz.Geometry.PairFamilyConstruction

/-!
# Pair families with native zero-dimensional ribbons

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160;
`def:chain`, lines 163–169; `sec:lean`, lines 788–797 and 825–830.
On a fixed ambient compact presentation, native zero-dimensional ribbon
data produce an actual pair deformation, including both completed families.
The prescribed maps and positive witnesses may vary with the parameter.

The map and witness regularity hypotheses concern the original native
source and ambient boundary and require smoothness on an open neighborhood
of the closed interval. No map is assumed smooth on the whole real line,
and positivity is required only on the interval. No ribbon primitive
compatibility equation, completion, collar, or presentation compatibility
is assumed. The fixed
ambient presentation and its Liouville structures remain input; producing
a boundary presentation for a native ambient family is a separate bridge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set

namespace FsFltz.Geometry.LiouvilleDomain.FlowCollar

/-- The two actual open restrictions of a zero-dimensional collar
localization retain the original compact carrier smoothly. -/
def originalPointDiffeomorph_of_dimension_zero {D : LiouvilleDomain 0}
    (C : FlowCollar D) :
    letI := C.localizedDomain.domain.zeroChartedSpace
    letI := D.domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0)
      C.localizedDomain.domain.Point D.domain.Point ∞ := by
  let := C.localizedDomain.domain.zeroChartedSpace
  let := D.domain.zeroChartedSpace
  let := C.localizedDomain.domain.discreteTopology_zero
  let := D.domain.discreteTopology_zero
  exact
    { toEquiv := ((D.neighborhoodDomain.restrictPointHomeomorph C.neighborhood
        C.carrier_subset_neighborhood).trans
          (D.domain.restrictPointHomeomorph D.symplecticNeighborhood
            D.carrier_subset_symplecticNeighborhood)).toEquiv
      contMDiff_toFun := contMDiff_of_discreteTopology
      contMDiff_invFun := contMDiff_of_discreteTopology }

@[simp] theorem originalPointDiffeomorph_of_dimension_zero_val
    {D : LiouvilleDomain 0} (C : FlowCollar D)
    (x : C.localizedDomain.domain.Point) :
    (C.originalPointDiffeomorph_of_dimension_zero x).val = x.val.val.val := rfl

end FsFltz.Geometry.LiouvilleDomain.FlowCollar

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- A prescribed injective map out of the native zero-dimensional manifold
is already a smooth embedding on that original source. -/
def nativeRibbonEmbedding (D : CompactDomain 2)
    (j : M → D.boundary.Point) (hj : Function.Injective j) :
    (sourceManifold M).SmoothEmbedding D.boundary := by
  let := source_discreteTopology M
  have hs : ContMDiff 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 1) ∞ j :=
    contMDiff_of_discreteTopology
  exact
    { map := ⟨j, hs⟩
      embedding := (hs.continuous.isClosedEmbedding hj).isEmbedding
      immersion := fun _ _ _ _ => PiLp.ext (fun i => Fin.elim0 i) }

/-- The compact ribbon's actual carrier diffeomorphism keeps the same
native points under both open restrictions of its constructed collar. -/
def localizedRibbonCarrierDiffeomorph
    (μ : (sourceManifold M).Form 1)
    (C : LiouvilleDomain.FlowCollar (liouvilleDomain M μ)) :
    letI := C.localizedDomain.domain.zeroChartedSpace
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M
      C.localizedDomain.domain.Point ∞ := by
  let := C.localizedDomain.domain.zeroChartedSpace
  let := (liouvilleDomain M μ).domain.zeroChartedSpace
  exact (carrierDiffeomorph μ).trans
    C.originalPointDiffeomorph_of_dimension_zero.symm

@[simp] theorem localizedRibbonCarrierDiffeomorph_val
    (μ : (sourceManifold M).Form 1)
    (C : LiouvilleDomain.FlowCollar (liouvilleDomain M μ)) (x : M) :
    (localizedRibbonCarrierDiffeomorph μ C x).val.val.val = x := rfl

/-- The full core of each actual constructed zero-dimensional completed
family transports to the whole original native manifold through the same
two inclusions as its compact presentation. -/
theorem image_localizedCompletionFamily_core
    (μ : Parameter → (sourceManifold M).Form 1) (t : Parameter) :
    (fun z : ((localizedCompletionFamily μ).collars t).localizedDomain.domain.extension.Point =>
      z.val.val) '' ((localizedCompletionFamily μ).collars t).cylindricalCompletion.core =
        (univ : Set M) := by
  rw [Completion.core_eq_carrier_of_dimension_zero]
  apply eq_univ_of_forall
  intro x
  exact ⟨(localizedRibbonCarrierDiffeomorph (μ t)
    ((localizedCompletionFamily μ).collars t) x).val,
    (localizedRibbonCarrierDiffeomorph (μ t)
      ((localizedCompletionFamily μ).collars t) x).property,
    localizedRibbonCarrierDiffeomorph_val (μ t)
      ((localizedCompletionFamily μ).collars t) x⟩


/-- Assemble one zero-dimensional native ribbon slice on the actual
localized ambient and ribbon completions. -/
def localizedZeroWitnessedPair
    (D : LiouvilleDomain 2) (μ : (sourceManifold M).Form 1)
    (A : LiouvilleDomain.FlowCollar D)
    (B : LiouvilleDomain.FlowCollar (liouvilleDomain M μ))
    (j : M → D.domain.boundary.Point) (hj : Function.Injective j)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) : WitnessedPair 1 :=
  localizedWitnessedPair D (liouvilleDomain M μ) A B
    (nativeRibbonEmbedding D.domain j hj) b hb hpositive
    (fun x _ => by
      change (sourceManifold M).pullback D.domain.boundary
        (nativeRibbonEmbedding D.domain j hj).map
        (fun y => b y • D.domain.boundaryForm D.liouville.primitive y) x = μ x
      rw [positiveForm_eq_zero M 0
        ((sourceManifold M).pullback D.domain.boundary _ _),
        positiveForm_eq_zero M 0 μ])

/-- The actual compact ribbon embedding commutes with the native carrier
diffeomorphism, retaining every prescribed point of the ribbon. -/
@[simp] theorem localizedZeroWitnessedPair_embedding
    (D : LiouvilleDomain 2) (μ : (sourceManifold M).Form 1)
    (A : LiouvilleDomain.FlowCollar D)
    (B : LiouvilleDomain.FlowCollar (liouvilleDomain M μ))
    (j : M → D.domain.boundary.Point) (hj : Function.Injective j)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) (x : M) :
    (localizedZeroWitnessedPair D μ A B j hj b hb hpositive).ribbonEmbedding.map
      (localizedRibbonCarrierDiffeomorph μ B x).val = j x := rfl

/-- The arbitrary original native primitive is preserved through the same
carrier inclusion used by the ribbon embedding. -/
theorem localizedZeroWitnessedPair_primitive
    (D : LiouvilleDomain 2) (μ : (sourceManifold M).Form 1)
    (A : LiouvilleDomain.FlowCollar D)
    (B : LiouvilleDomain.FlowCollar (liouvilleDomain M μ))
    (j : M → D.domain.boundary.Point) (hj : Function.Injective j)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) :
    (sourceManifold M).pullback
      (localizedZeroWitnessedPair D μ A B j hj b hb hpositive).ribbonDomain.domain.extension
      (fun x => (localizedRibbonCarrierDiffeomorph μ B x).val)
      (localizedZeroWitnessedPair D μ A B j hj b hb hpositive).ribbonDomain.liouville.primitive = μ := by
  rw [positiveForm_eq_zero M 0 ((sourceManifold M).pullback _ _ _),
    positiveForm_eq_zero M 0 μ]

/-- Localization retains the supplied positive witness literally. -/
@[simp] theorem localizedZeroWitnessedPair_witness
    (D : LiouvilleDomain 2) (μ : (sourceManifold M).Form 1)
    (A : LiouvilleDomain.FlowCollar D)
    (B : LiouvilleDomain.FlowCollar (liouvilleDomain M μ))
    (j : M → D.domain.boundary.Point) (hj : Function.Injective j)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) :
    (localizedZeroWitnessedPair D μ A B j hj b hb hpositive).witness = b := rfl

/-- The actual complete flow's full embedded core is precisely the entire
original native ribbon image. This uses the zero-dimensional flow theorem
and the surjective native carrier diffeomorphism. -/
theorem localizedZeroWitnessedPair_embeddedCore
    (D : LiouvilleDomain 2) (μ : (sourceManifold M).Form 1)
    (A : LiouvilleDomain.FlowCollar D)
    (B : LiouvilleDomain.FlowCollar (liouvilleDomain M μ))
    (j : M → D.domain.boundary.Point) (hj : Function.Injective j)
    (b : D.domain.boundary.Point → ℝ)
    (hb : ContMDiff 𝓘(ℝ, Model 1) 𝓘(ℝ, ℝ) ∞ b)
    (hpositive : ∀ x, 0 < b x) :
    (localizedZeroWitnessedPair D μ A B j hj b hb hpositive).embeddedCore = range j := by
  let P := localizedZeroWitnessedPair D μ A B j hj b hb hpositive
  rw [P.embeddedCore_eq_ribbon_of_rank_one]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, hx⟩ := (localizedRibbonCarrierDiffeomorph μ B).surjective ⟨z, hz⟩
    refine ⟨x, ?_⟩
    rw [← localizedZeroWitnessedPair_embedding D μ A B j hj b hb hpositive x]
    exact congrArg (fun w => P.ribbonEmbedding.map w.val) hx
  · rintro ⟨x, rfl⟩
    exact ⟨(localizedRibbonCarrierDiffeomorph μ B x).val,
      (localizedRibbonCarrierDiffeomorph μ B x).property,
      localizedZeroWitnessedPair_embedding D μ A B j hj b hb hpositive x⟩


/-- Native zero-dimensional ribbon families produce actual pair
deformations, including the completed families. The formula retains the
time-dependent embeddings and witnesses rather than replacing either by
its reference slice. -/
theorem exists_native_zero_pairDeformation_on_fixed_ambient
    (D : CompactDomain 2) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (μ : Parameter → (sourceManifold M).Form 1)
    (j : Parameter → M → D.boundary.Point)
    (hj : ∀ t, Function.Injective (j t))
    (hjs : (sourceManifold M).IsSmoothIntervalMapFamily D.boundary j)
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x) :
    ∃ A : (t : Parameter) → LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain 2),
      ∃ B : (t : Parameter) → LiouvilleDomain.FlowCollar (liouvilleDomain M (μ t)),
        ∃ Q : PairDeformation 1,
          (Q.pair = fun t => localizedZeroWitnessedPair ⟨D, L t⟩ (μ t)
            (A t) (B t) (j t) (hj t) (b t) (hb.contMDiff_slice t) (hpositive t)) ∧
          ∀ t, (localizedZeroWitnessedPair ⟨D, L t⟩ (μ t) (A t) (B t)
            (j t) (hj t) (b t) (hb.contMDiff_slice t) (hpositive t)).embeddedCore = range (j t) := by
  obtain ⟨A, B, Q, hQ⟩ :=
    CompactDomain.exists_localized_pairDeformation (n := 1) D (compactDomain M) L (liouvilleFamily μ)
    (fun t => nativeRibbonEmbedding D (j t) (hj t)) b hL
    (primitiveFamily_smooth μ) hjs hb hpositive
    (fun t x _ => by
      change (sourceManifold M).pullback D.boundary
        (nativeRibbonEmbedding D (j t) (hj t)).map
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = μ t x
      rw [positiveForm_eq_zero M 0 ((sourceManifold M).pullback D.boundary _ _),
        positiveForm_eq_zero M 0 (μ t)])
  refine ⟨A, B, Q, hQ, ?_⟩
  intro t
  exact localizedZeroWitnessedPair_embeddedCore ⟨D, L t⟩ (μ t) (A t) (B t)
    (j t) (hj t) (b t) (hb.contMDiff_slice t) (hpositive t)

end FsFltz.Geometry.IntrinsicZeroLiouville
