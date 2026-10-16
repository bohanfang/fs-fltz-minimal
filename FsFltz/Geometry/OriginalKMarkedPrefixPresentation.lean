import FsFltz.Geometry.OriginalKMarkedPrefix
import FsFltz.Geometry.CompletionMapUniqueness

/-!
# Attach an independently supplied original initial-pair presentation

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199,
`lem:choices`, lines 437–474, and `sec:lean`, lines 788–814;
`geometric-part-fsf-proof.tex`, `lem:choices`, lines 950–973, and
`sec:assembly`, lines 2195–2208 and 2225–2243.
Equal complete compact images determine a strict pair identification.
Its identity on the entire marked logarithmic ambient is proved from
primitive preservation and its compact square. This handles arbitrary
presentations at fixed choices. Moving the ribbon level or rounding
remains the separate initial-choice comparison obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

namespace InitialPairData

variable {n : ℕ} {I : ToricInput n} {R K Aminus A : ℝ} {m : RoundingChoice}

/-- The given inclusion square retains the actual whole embedded ribbon. -/
theorem embeddedRibbon_image (S : InitialPairData I R K Aminus A m) :
    (S.domainEmbedding.comp
      (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)).map ''
        S.pair.ribbonDomain.domain.carrier = InitialRibbon I R Aminus := by
  calc
    _ = (fun x => S.fiber.embedding.map (S.ribbonInFiber.map x)) ''
        S.pair.ribbonDomain.domain.carrier := Set.image_congr S.ribbon_square
    _ = _ := S.ribbon_image

/-- The full fiber marking determines the ribbon primitive on its entire
compact carrier, including the boundary derivatives. -/
theorem embeddedRibbon_pullback_on_carrier (S : InitialPairData I R K Aminus A m)
    (x : S.pair.ribbonDomain.domain.extension.Point) (hx : x ∈ S.pair.ribbonDomain.domain.carrier) :
    S.pair.ribbonDomain.liouville.primitive x =
      S.pair.ribbonDomain.domain.extension.pullback (lgManifold n)
        (S.domainEmbedding.comp
          (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)).map
        (lambda0Form n) x := by
  let j := S.domainEmbedding.comp
    (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)
  have h := S.fiberMarking.pullback_primitive_on_carrier S.ribbonInFiber (fun _ => rfl) x hx
  rw [← S.fiber.primitive] at h
  rw [← S.pair.ribbonDomain.domain.extension.pullback_comp S.fiber.ambient.manifold (lgManifold n)
    (S.ribbonInFiber.map.contMDiff.mdifferentiable (by simp))
    (S.fiber.embedding.map.contMDiff.mdifferentiable (by simp))] at h
  have he := S.pair.ribbonDomain.domain.pullback_eq_of_eqOn_carrier (lgManifold n)
    j.map (S.fiber.embedding.comp S.ribbonInFiber).map S.ribbon_square (lambda0Form n) x hx
  exact h.symm.trans he.symm

/-- Any two supplied representations of the same literal choices admit an
actual strict identification, pointwise on their whole embedded compact
pieces and equal to the identity on the entire marked ambient. No map or
chain is assumed, and dimension zero ribbons are included. -/
theorem exists_sameChoice_identification (S T : InitialPairData I R K Aminus A m) :
    ∃ q : CompletionIdentification S.pair T.pair,
      q.scale = 1 ∧ q.shift = (fun _ => 0) ∧
      q.ambientEquiv.trans T.ambientMarking.equiv = S.ambientMarking.equiv ∧
      ∀ x ∈ S.pair.ribbonDomain.domain.carrier,
        (T.domainEmbedding.comp
          (T.pair.ambientDomain.domain.boundaryInclusion.comp T.pair.ribbonEmbedding)).map
            (q.ribbonEquiv.map x) =
        (S.domainEmbedding.comp
          (S.pair.ambientDomain.domain.boundaryInclusion.comp S.pair.ribbonEmbedding)).map x := by
  have hE : S.pair.ambientDomain.domain.carrier.Nonempty := by
    obtain ⟨x, _hx⟩ := S.ribbon_nonempty
    exact ⟨S.pair.ambientDomain.domain.boundaryInclusion.map (S.pair.ribbonEmbedding.map x),
      S.pair.ambientDomain.domain.boundaryInclusion_mem_carrier _⟩
  obtain ⟨q, hscale, hshift, hribbon, hcompact⟩ :=
    CompletionIdentification.exists_of_commonEmbeddedPair_onCarrier
      S.pair T.pair hE S.ribbon_nonempty S.domainEmbedding T.domainEmbedding
      (S.domain_image.trans T.domain_image.symm)
      (S.embeddedRibbon_image.trans T.embeddedRibbon_image.symm)
      (lambdaKForm I K) (lambda0Form n)
      (fun x hx => (S.ambientMarking.pullback_primitive_on_carrier
        S.domainEmbedding (fun _ => rfl) x hx).symm)
      (fun x hx => (T.ambientMarking.pullback_primitive_on_carrier
        T.domainEmbedding (fun _ => rfl) x hx).symm)
      S.embeddedRibbon_pullback_on_carrier T.embeddedRibbon_pullback_on_carrier
  refine ⟨q, hscale, hshift, ?_, hribbon⟩
  apply S.pair.ambientCompletion.equiv_eq_of_scaled_primitive_on_compact
    S.ambient.toCompleteLiouvilleManifold
    (q.ambientEquiv.trans T.ambientMarking.equiv) S.ambientMarking.equiv 1 1
  · change S.pair.ambientManifold.pullback (lgManifold n)
      (T.ambientMarking.equiv ∘ q.ambientEquiv) (lambdaKForm I K) = _
    have hpT : T.pair.ambientManifold.pullback (lgManifold n)
        T.ambientMarking.equiv (lambdaKForm I K) =
        T.pair.ambientCompletion.ambient.primitive := T.ambientMarking.primitive
    rw [S.pair.ambientManifold.pullback_comp T.pair.ambientManifold (lgManifold n)
      (q.ambientEquiv.mdifferentiable (by simp))
      (T.ambientMarking.equiv.mdifferentiable (by simp)), hpT,
      q.primitive, one_smul]
  · simpa only [one_smul] using S.ambientMarking.primitive
  · intro x hx
    obtain ⟨y, hy, himage, hq⟩ := hcompact x hx
    change T.ambientMarking.equiv (q.ambientEquiv (S.pair.ambientCompletion.inclusion.map x)) =
      S.ambientMarking.equiv (S.pair.ambientCompletion.inclusion.map x)
    rw [hq, T.ambientMarking.inclusion ⟨y, hy⟩, S.ambientMarking.inclusion ⟨x, hx⟩]
    exact himage

end InitialPairData

namespace Geometry

/-- A prescribed logarithmic tensor pulls back through the actual composite
marking. The almost complex structure is transported with that tensor. -/
theorem IsLogarithmicGrading.pullbackTo {n : ℕ} {M N : SmoothManifold (2 * n)}
    {η : M.Form 2} {ξ : N.Form 2} {u : MaslovRepresentative N ξ}
    (f : M.SmoothEquiv N) (g : N.SmoothEquiv (lgManifold n))
    (hη : M.pullback N f ξ = η) (hu : IsLogarithmicGrading g u) :
    IsLogarithmicGrading (f.trans g) (u.pullbackTo f hη) := by
  intro x v
  change u.tensor (f x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i)) = _
  rw [hu]
  apply congrArg coordinateSquaredVolumeValue
  funext i
  rw [logarithmicTangentCoordinates_naturality N g,
    logarithmicTangentCoordinates_naturality M (f.trans g)]
  have hd := mfderiv_comp x (g.mdifferentiable (by simp) (f x)) (f.mdifferentiable (by simp) x)
  change logarithmicTangentCoordinates (lgManifold n) id (g (f x))
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g (f x)
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x (v i))) =
    logarithmicTangentCoordinates (lgManifold n) id (g (f x))
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (g ∘ f) x (v i))
  rw [hd]
  rfl

/-- Grading lifts compose on precisely the concatenated geometric path. -/
def GradedComparisonChain.comp {n : ℕ} {P Q R : WitnessedPair n}
    {C : ComparisonChain P Q} {D : ComparisonChain Q R}
    {s : P.Maslov} {u : Q.Maslov} {v : R.Maslov}
    (g : GradedComparisonChain P C s u) (h : GradedComparisonChain Q D u v) :
    GradedComparisonChain P (C.comp D) s v := by
  induction h with
  | nil => exact g
  | cons initial last ih => exact .cons (ih g) last

end Geometry

/-- Attach any independently supplied initial-pair presentation at these
same choices. The new identification is proved identity on marked Y and
graded on the same actual map. The two-arrow initial segment and the full
six-arrow chain retain their literal supplied source and marked endpoint. -/
theorem PotentialTailoringOriginalMarkedPrefix.exists_supplied_source_chain {n : ℕ}
    {I : ToricInput n} {φ : RealSpace n → ℝ} {β Cplus Aminus originalK K : ℝ}
    {m : RoundingChoice}
    (P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus Aminus originalK K m)
    (S : InitialPairData I (Real.exp β) originalK Aminus (Cplus ^ 2 * β ^ 2 / 2) m) :
    ∃ q : CompletionIdentification S.pair P.original.pair,
    ∃ s : S.pair.Maslov,
    ∃ C : ComparisonChain S.pair P.matching.pair,
      q.scale = 1 ∧ q.shift = (fun _ => 0) ∧
      q.ambientEquiv.trans P.original.ambientMarking.equiv = S.ambientMarking.equiv ∧
      IsLogarithmicGrading S.ambientMarking.equiv s ∧ C.length = 2 ∧
      Nonempty (GradedComparisonChain S.pair C s P.matchingMaslov) ∧
      ∃ D : ComparisonChain S.pair P.marked.tailoring.deformation.target, D.length = 6 ∧
        D = (C.cons (.identification P.junction)).comp P.marked.chain := by
  obtain ⟨q, hscale, hshift, hmark, _hribbon⟩ := S.exists_sameChoice_identification P.original
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
  refine ⟨q, s, C, hscale, hshift, hmark, hs, hC,
    ⟨gE.comp P.original_grading⟩, D, hD, ?_⟩
  change E.comp ((P.original_chain.cons (.identification P.junction)).comp P.marked.chain) = _
  rw [← Quiver.Path.comp_assoc, Quiver.Path.comp_cons]

end FsFltz
