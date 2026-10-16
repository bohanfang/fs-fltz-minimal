import FsFltz.Geometry.OriginalKMarkedPrefixPresentation
import FsFltz.Geometry.BoundaryContact
import FsFltz.InitialChoices

/-!
# Original initial choices with the same full-ribbon level

Source: `geoemtric-part-fsf.tex`, `lem:choices`, lines 437–474, and
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 950–973, especially
lines 961–964. The strict ambient map is constructed from the two actual
inclusion markings. Its induced boundary map fixes the whole common
embedded ribbon, even when the rounded ambient domains differ.
Varying the ribbon level still requires a smooth completed pair family.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.InitialPairData
open Geometry Geometry.SmoothManifold

variable {n : ℕ} {I : ToricInput n} {R K Aminus A B : ℝ}
  {m p : RoundingChoice}

/-- Different ambient truncations and roundings of the same whole ribbon
have an actual strict identification, identity on the entire marked Y.
The boundary shift vanishes on the entire ribbon, not only on its core. -/
theorem exists_fixedRibbon_identification
    (S : InitialPairData I R K Aminus A m)
    (T : InitialPairData I R K Aminus B p) :
    ∃ q : CompletionIdentification S.pair T.pair,
      q.scale = 1 ∧
      q.ambientEquiv.trans T.ambientMarking.equiv = S.ambientMarking.equiv ∧
      (∀ x ∈ S.pair.ribbonDomain.domain.carrier, q.shift (S.pair.ribbonEmbedding.map x) = 0) ∧
      ∀ x ∈ S.pair.ribbonDomain.domain.carrier,
        (T.domainEmbedding.comp
          (T.pair.ambientDomain.domain.boundaryInclusion.comp T.pair.ribbonEmbedding)).map
            (q.ribbonEquiv.map x) =
        (S.domainEmbedding.comp
          (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)).map x := by
  let f := S.ambientMarking.equiv.trans T.ambientMarking.equiv.symm
  have hmark (x : S.pair.ambientManifold.Point) :
      T.ambientMarking.equiv (f x) = S.ambientMarking.equiv x :=
    T.ambientMarking.equiv.apply_symm_apply _
  have hp : S.pair.ambientManifold.pullback T.pair.ambientManifold f
      T.pair.ambientCompletion.ambient.primitive =
        S.pair.ambientCompletion.ambient.primitive := by
    have hpT : T.pair.ambientManifold.pullback (lgManifold n)
        T.ambientMarking.equiv (lambdaKForm I K) =
          T.pair.ambientCompletion.ambient.primitive := T.ambientMarking.primitive
    rw [← hpT]
    rw [← S.pair.ambientManifold.pullback_comp T.pair.ambientManifold (lgManifold n)
      (f.mdifferentiable (by simp)) (T.ambientMarking.equiv.mdifferentiable (by simp))]
    rw [show T.ambientMarking.equiv ∘ f = S.ambientMarking.equiv from funext hmark]
    exact S.ambientMarking.primitive
  obtain ⟨ψ, shift, hshift, hend, hboundary⟩ :=
    S.pair.ambientCompletion.exists_boundaryEquiv_with_pullback T.pair.ambientCompletion f hp
  let jS := S.domainEmbedding.comp
    (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)
  let jT := T.domainEmbedding.comp
    (T.pair.ambientDomain.domain.boundaryInclusion.comp T.pair.ribbonEmbedding)
  obtain ⟨r, hr, _hrinverse⟩ :=
    S.pair.ribbonDomain.domain.exists_compactDiffeomorph_of_embeddedCarrier
      T.pair.ribbonDomain.domain (lgManifold n) S.ribbon_nonempty jS jT
      (S.embeddedRibbon_image.trans T.embeddedRibbon_image.symm)
  have hrprimitive (x : S.pair.ribbonDomain.domain.extension.Point)
      (hx : x ∈ S.pair.ribbonDomain.domain.carrier) :
      S.pair.ribbonDomain.domain.extension.pullback T.pair.ribbonDomain.domain.extension
        r.map T.pair.ribbonDomain.liouville.primitive x =
        S.pair.ribbonDomain.liouville.primitive x := by
    calc
      _ = S.pair.ribbonDomain.domain.extension.pullback T.pair.ribbonDomain.domain.extension
          r.map (T.pair.ribbonDomain.domain.extension.pullback (lgManifold n) jT.map
            (lambda0Form n)) x := by
              unfold SmoothManifold.pullback
              rw [T.embeddedRibbon_pullback_on_carrier (r.map x) (r.maps_source hx)]
              rfl
      _ = S.pair.ribbonDomain.domain.extension.pullback (lgManifold n) jS.map
          (lambda0Form n) x := r.pullback_of_embeddedCarrier (lgManifold n) jS jT hr _ x hx
      _ = _ := (S.embeddedRibbon_pullback_on_carrier x hx).symm
  have hsection (x : S.pair.ribbonDomain.domain.extension.Point)
      (hx : x ∈ S.pair.ribbonDomain.domain.carrier) :
      f (S.pair.ambientCompletion.inclusion.map
        (S.pair.ambientDomain.domain.boundaryInclusion.map (S.pair.ribbonEmbedding.map x))) =
      T.pair.ambientCompletion.inclusion.map
        (T.pair.ambientDomain.domain.boundaryInclusion.map (T.pair.ribbonEmbedding.map (r.map x))) := by
    apply T.ambientMarking.equiv.injective
    change T.ambientMarking.equiv (f (S.pair.ambientCompletion.inclusion.map
      (S.pair.ambientDomain.domain.boundaryInclusion.map (S.pair.ribbonEmbedding.map x)))) =
      T.ambientMarking.equiv (T.pair.ambientCompletion.inclusion.map
        (T.pair.ambientDomain.domain.boundaryInclusion.map (T.pair.ribbonEmbedding.map (r.map x))))
    rw [hmark,
      S.ambientMarking.inclusion ⟨_, S.pair.ambientDomain.domain.boundaryInclusion_mem_carrier _⟩,
      T.ambientMarking.inclusion ⟨_, T.pair.ambientDomain.domain.boundaryInclusion_mem_carrier _⟩]
    exact (hr x hx).symm
  have hcoordinates (x : S.pair.ribbonDomain.domain.extension.Point)
      (hx : x ∈ S.pair.ribbonDomain.domain.carrier) :
      ψ (S.pair.ribbonEmbedding.map x) = T.pair.ribbonEmbedding.map (r.map x) ∧
      shift (S.pair.ribbonEmbedding.map x) = 0 := by
    have he := hend (S.pair.ribbonEmbedding.map x) 0
    simp only [Completion.endMap_zero, zero_add] at he
    rw [hsection x hx] at he
    have hz := T.pair.ambientCompletion.endMap_zero (T.pair.ribbonEmbedding.map (r.map x))
    exact Prod.mk.inj (T.pair.ambientCompletion.endMap_injective (he.symm.trans hz.symm))
  let q : CompletionIdentification S.pair T.pair :=
    { ambientEquiv := f
      primitive := hp
      boundaryEquiv := ψ
      shift := shift
      smooth_shift := hshift
      induced_at_infinity := fun x => ⟨0, fun r _ => hend x r⟩
      boundary_primitive := hboundary
      ribbonEquiv := r
      scale := 1
      positive_scale := zero_lt_one
      ribbon_primitive := fun x hx => by simpa only [one_smul] using hrprimitive x hx
      ribbon_square := fun x hx => (hcoordinates x hx).1 }
  refine ⟨q, rfl, Diffeomorph.ext hmark, ?_, hr⟩
  exact fun x hx => (hcoordinates x hx).2

/-- Expose the actual supplied inclusion marking in the fixed-ambient
comparison interface. Its compact primitive square follows from the same
marking, including points on the native domain boundary. -/
def fixedAmbientMarking (S : InitialPairData I R K Aminus A m) :
    FixedAmbientPairMarking I K S.pair where
  domainEmbedding := S.domainEmbedding
  equiv := S.ambientMarking.equiv
  primitive := S.ambientMarking.primitive
  compact_square := fun x hx => S.ambientMarking.inclusion ⟨x, hx⟩
  domain_primitive := fun x hx =>
    S.ambientMarking.pullback_primitive_on_carrier S.domainEmbedding (fun _ => rfl) x hx

/-- The actual one-step fixed-ribbon comparison carries the logarithmic
datum and retains any supplied target representative literally. All
ambient levels, rounding profiles and pair presentations are arbitrary. -/
theorem exists_fixedRibbon_comparison_to_datum
    (S : InitialPairData I R K Aminus A m)
    (T : InitialPairData I R K Aminus B p)
    (u : T.pair.Maslov) (hu : IsLogarithmicGrading T.ambientMarking.equiv u) :
    ∃ C : InitialChoiceComparison S T, C.chain.length = 1 ∧ C.targetDatum = u := by
  obtain ⟨q, _hscale, hmark, _hshift, _hribbon⟩ := S.exists_fixedRibbon_identification T
  let s := u.pullbackTo q.ambientEquiv q.pullback_symplecticForm
  have hs : IsLogarithmicGrading S.ambientMarking.equiv s := by
    rw [← hmark]
    exact hu.pullbackTo q.ambientEquiv T.ambientMarking.equiv q.pullback_symplecticForm
  obtain ⟨gq⟩ := (q.gradedLift_iff_class_eq s u).mpr rfl
  let C : InitialChoiceComparison S T :=
    { sourceMarking := S.fixedAmbientMarking
      targetMarking := T.fixedAmbientMarking
      source_embedding := rfl
      target_embedding := rfl
      source_marking := rfl
      target_marking := rfl
      chain := Quiver.Path.nil.cons (.identification q)
      fixedAmbient := .cons (.nil S.fixedAmbientMarking) (.identification (fun x => by
        exact DFunLike.congr_fun hmark x))
      sourceDatum := s
      targetDatum := u
      source_prescribed := hs
      target_prescribed := hu
      graded := .cons (.nil s) (.identification gq) }
  exact ⟨C, rfl, rfl⟩

end FsFltz.InitialPairData

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Attach any supplied ambient truncation and rounding profile at the
convenient full-ribbon level. The actual source and retained endpoint
occur in the same six-arrow path; its first two arrows are graded. -/
theorem PotentialTailoringOriginalMarkedPrefix.exists_fixedRibbon_supplied_source_chain {n : ℕ}
    {I : ToricInput n} {φ : RealSpace n → ℝ} {β Cplus Aminus originalK K A : ℝ}
    {m p : RoundingChoice}
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (S : InitialPairData I (Real.exp β) originalK Aminus A p) :
    ∃ q : CompletionIdentification S.pair P.original.pair,
    ∃ s : S.pair.Maslov,
    ∃ C : ComparisonChain S.pair P.matching.pair,
      q.scale = 1 ∧
      q.ambientEquiv.trans P.original.ambientMarking.equiv = S.ambientMarking.equiv ∧
      IsLogarithmicGrading S.ambientMarking.equiv s ∧ C.length = 2 ∧
      C = (Quiver.Path.nil.cons (ComparisonStep.identification q)).comp P.original_chain ∧
      Nonempty (GradedComparisonChain S.pair C s P.matchingMaslov) ∧
      ∃ D : ComparisonChain S.pair P.marked.tailoring.deformation.target, D.length = 6 ∧
        D = (C.cons (.identification P.junction)).comp P.marked.chain := by
  obtain ⟨q, hscale, hmark, _hshift, _hribbon⟩ := S.exists_fixedRibbon_identification P.original
  let s := P.originalMaslov.pullbackTo q.ambientEquiv q.pullback_symplecticForm
  have hs : IsLogarithmicGrading S.ambientMarking.equiv s := by
    rw [← hmark]
    exact P.original_prescribed.pullbackTo q.ambientEquiv P.original.ambientMarking.equiv
      q.pullback_symplecticForm
  obtain ⟨gq⟩ := (q.gradedLift_iff_class_eq s P.originalMaslov).mpr rfl
  let E : ComparisonChain S.pair P.original.pair := Quiver.Path.nil.cons (.identification q)
  let C := E.comp P.original_chain
  have gE : GradedComparisonChain S.pair E s P.originalMaslov :=
    .cons (.nil s) (.identification gq)
  have hC : C.length = 2 := by simp [C, E, Quiver.Path.length_comp, P.original_length]
  let D := E.comp P.chain
  have hD : D.length = 6 := by simp [D, E, Quiver.Path.length_comp]
  refine ⟨q, s, C, hscale, hmark, hs, hC, rfl, ⟨gE.comp P.original_grading⟩, D, hD, ?_⟩
  change E.comp ((P.original_chain.cons (.identification P.junction)).comp P.marked.chain) = _
  rw [← Quiver.Path.comp_assoc, Quiver.Path.comp_cons]

end FsFltz
