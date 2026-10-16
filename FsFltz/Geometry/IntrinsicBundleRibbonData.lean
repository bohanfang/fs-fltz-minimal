import FsFltz.Geometry.IntrinsicBundleBoundaryTransport
import FsFltz.Geometry.IntrinsicBundleTargetComposition
import FsFltz.Geometry.IntrinsicBundleBoundaryDiffeomorph

/-!
# Original-atlas ribbon maps under two bundle trivializations

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169, and
`sec:lean`, lines 788–814. Ribbon maps are specified only on pairs of
original bundle charts. Covariance is the literal square for the actual
source and ambient transitions. Compatible presentations retain all
original ribbon points, not merely their embedded cores.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle

namespace FsFltz.Geometry.IntrinsicSmoothBundle

variable {d a : ℕ} {H M : Type*} [TopologicalSpace H] [TopologicalSpace M]
  {I : ModelWithCorners ℝ (Model d) H} [ChartedSpace H M]
  {A : Type} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  {ER : Parameter → Type*} [∀ t, TopologicalSpace (ER t)]
  [TopologicalSpace (TotalSpace M ER)] [SmoothCompactBundle I (F := M) ER]
  {EA : Parameter → Type*} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]

/-- Source ribbon maps on pairs of original atlas charts, with actual
boundary target values and the literal coordinate square on overlaps. -/
structure BundleRibbonData (I : ModelWithCorners ℝ (Model d) H)
    (ER : Parameter → Type*) [∀ t, TopologicalSpace (ER t)]
    [TopologicalSpace (TotalSpace M ER)] [SmoothCompactBundle I (F := M) ER]
    (EA : Parameter → Type*) [∀ t, TopologicalSpace (EA t)]
    [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA] where
  map : {e : Trivialization M (π M ER) // e ∈ trivializationAtlas M ER} →
    {e : Trivialization A (π A EA) // e ∈ trivializationAtlas A EA} →
    Parameter → M → IntrinsicBoundary.Point a A
  smooth : ∀ (eR : {e : Trivialization M (π M ER) // e ∈ trivializationAtlas M ER})
    (eA : {e : Trivialization A (π A EA) // e ∈ trivializationAtlas A EA}),
    HasSmoothTargetFamilyOn I (IntrinsicBoundary.smoothManifold a A)
    (eR.val.baseSet ∩ eA.val.baseSet) (map eR eA)
  covariance : ∀ (eR cR : {e : Trivialization M (π M ER) // e ∈ trivializationAtlas M ER})
    (eA cA : {e : Trivialization A (π A EA) // e ∈ trivializationAtlas A EA}), ∀ t ∈
      (eR.val.baseSet ∩ cR.val.baseSet) ∩ (eA.val.baseSet ∩ cA.val.baseSet), ∀ x,
    (map cR cA t (eR.val.coordChange cR.val t x)).val =
      eA.val.coordChange cA.val t (map eR eA t x).val

namespace BundleRibbonData

/-- The ribbon map in two compatible presentations is constructed by
precomposing with the source transition and postcomposing with the actual
induced boundary transition. Timewise chart choices are eliminated in the
local coherence theorem below. -/
def mapInTrivializations (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA) :
    Parameter → M → IntrinsicBoundary.Point a A := fun t x =>
  let cR := trivializationAt M ER t
  let cA := trivializationAt A EA t
  boundaryFamilyOn (cA.baseSet ∩ eA.baseSet) (cA.coordChange eA)
    (compatibleTransition_boundary cA eA
      (compatibleTrivialization_of_mem (trivialization_mem_atlas A EA t)) heA) t
    (P.map ⟨cR, trivialization_mem_atlas M ER t⟩
      ⟨cA, trivialization_mem_atlas A EA t⟩ t (eR.coordChange cR t x))

theorem mapInTrivializations_val (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    {t : Parameter} (ht : t ∈ eA.baseSet) (x : M) :
    (P.mapInTrivializations eR eA heA t x).val =
      (trivializationAt A EA t).coordChange eA t
        (P.map ⟨trivializationAt M ER t, trivialization_mem_atlas M ER t⟩
          ⟨trivializationAt A EA t, trivialization_mem_atlas A EA t⟩ t
          (eR.coordChange (trivializationAt M ER t) t x)).val := by
  unfold mapInTrivializations
  exact boundaryFamilyOn_val
    (compatibleTransition_boundary (trivializationAt A EA t) eA
      (compatibleTrivialization_of_mem (trivialization_mem_atlas A EA t)) heA)
    ⟨mem_baseSet_trivializationAt A EA t, ht⟩ _

/-- Any fixed original pair of charts gives the same actual ribbon map
on the fourfold overlap. This proof consumes the source covariance and
the actual cocycles of both bundles. -/
theorem mapInTrivializations_eq_local_val
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (x : M) :
    (P.mapInTrivializations eR eA heA t x).val = cA.coordChange eA t
      (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t (eR.coordChange cR t x)).val := by
  let dR := trivializationAt M ER t
  let dA := trivializationAt A EA t
  have hdR : dR ∈ trivializationAtlas M ER := trivialization_mem_atlas _ _ _
  have hdA : dA ∈ trivializationAtlas A EA := trivialization_mem_atlas _ _ _
  have htR : t ∈ dR.baseSet := mem_baseSet_trivializationAt _ _ _
  have htA : t ∈ dA.baseSet := mem_baseSet_trivializationAt _ _ _
  rw [P.mapInTrivializations_val eR eA heA ht.2.1 x]
  have hsource : eR.coordChange dR t x = cR.coordChange dR t (eR.coordChange cR t x) :=
    (eR.coordChange_coordChange cR dR ht.1.1 ht.1.2 x).symm
  change dA.coordChange eA t
    (P.map ⟨dR, hdR⟩ ⟨dA, hdA⟩ t (eR.coordChange dR t x)).val = _
  rw [hsource, P.covariance ⟨cR, hcR⟩ ⟨dR, hdR⟩ ⟨cA, hcA⟩ ⟨dA, hdA⟩ t
    ⟨⟨ht.1.2, htR⟩, ⟨ht.2.2, htA⟩⟩]
  exact cA.coordChange_coordChange dA eA ht.2.2 htA _

/-- Coherence is an equality of actual boundary-valued maps, ready for
transporting the original local target germs. -/
theorem mapInTrivializations_eq_local
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet)) :
    P.mapInTrivializations eR eA heA t = fun x =>
      boundaryFamilyOn (cA.baseSet ∩ eA.baseSet) (cA.coordChange eA)
        (compatibleTransition_boundary cA eA (compatibleTrivialization_of_mem hcA) heA) t
        (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t (eR.coordChange cR t x)) := by
  funext x
  apply Subtype.ext
  rw [boundaryFamilyOn_val
    (compatibleTransition_boundary cA eA (compatibleTrivialization_of_mem hcA) heA)
    ⟨ht.2.2, ht.2.1⟩]
  exact P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x

/-- All original local ribbon values are recovered in their own original
pair of charts. -/
theorem mapInTrivializations_eq_original
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (heR : eR ∈ trivializationAtlas M ER)
    (eA : Trivialization A (π A EA)) (heA : eA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ eR.baseSet ∩ eA.baseSet) :
    P.mapInTrivializations eR eA (compatibleTrivialization_of_mem heA) t =
      P.map ⟨eR, heR⟩ ⟨eA, heA⟩ t := by
  funext x
  apply Subtype.ext
  rw [P.mapInTrivializations_eq_local_val eR eA (compatibleTrivialization_of_mem heA)
    eR heR eA heA ⟨⟨ht.1, ht.1⟩, ⟨ht.2, ht.2⟩⟩ x,
    eR.coordChange_same ht.1, eA.coordChange_same ht.2]
  rfl

/-- Changing both compatible presentations retains the whole literal
ribbon map in the coordinate square. -/
theorem mapInTrivializations_covariance_val
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR cR : Trivialization M (π M ER)) (eA cA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (hcA : CompatibleTrivialization (𝓡∂ (a + 1)) EA cA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (x : M) :
    (P.mapInTrivializations cR cA hcA t (eR.coordChange cR t x)).val =
      eA.coordChange cA t (P.mapInTrivializations eR eA heA t x).val := by
  rw [P.mapInTrivializations_val cR cA hcA ht.2.2,
    P.mapInTrivializations_val eR eA heA ht.2.1,
    eR.coordChange_coordChange cR (trivializationAt M ER t) ht.1.1 ht.1.2,
    (trivializationAt A EA t).coordChange_coordChange eA cA
      (mem_baseSet_trivializationAt _ _ _) ht.2.1]

/-- Equality of the entire embedded ribbon images follows from the
actual local coordinate expression and the surjective source transition. -/
theorem range_mapInTrivializations_val
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet)) :
    range (fun x => (P.mapInTrivializations eR eA heA t x).val) =
      cA.coordChange eA t '' range (fun y => (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t y).val) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨eR.coordChange cR t x, rfl⟩,
      (P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x).symm⟩
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    obtain ⟨x, hxy⟩ := (eR.coordChangeHomeomorph cR ht.1.1 ht.1.2).surjective y
    refine ⟨x, ?_⟩
    change (P.mapInTrivializations eR eA heA t x).val =
      cA.coordChange eA t (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t y).val
    change eR.coordChange cR t x = y at hxy
    rw [P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x, hxy]

/-- An original local ribbon embedding remains an embedding in the
constructed presentations, using the actual two chart homeomorphisms. -/
theorem isEmbedding_mapInTrivializations
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (hj : Topology.IsEmbedding (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t)) :
    Topology.IsEmbedding (P.mapInTrivializations eR eA heA t) := by
  apply Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp
  have h := (cA.coordChangeHomeomorph eA ht.2.2 ht.2.1).isEmbedding.comp
    ((Topology.IsEmbedding.subtypeVal.comp hj).comp
      (eR.coordChangeHomeomorph cR ht.1.1 ht.1.2).isEmbedding)
  have heq : (Subtype.val : IntrinsicBoundary.Point a A → A) ∘
      (P.mapInTrivializations eR eA heA t) =
      (cA.coordChangeHomeomorph eA ht.2.2 ht.2.1) ∘
        ((Subtype.val : IntrinsicBoundary.Point a A → A) ∘
          (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t)) ∘
        (eR.coordChangeHomeomorph cR ht.1.1 ht.1.2) := by
    funext x
    exact P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x
  rw [heq]
  exact h

/-- Injectivity of an original ribbon map is preserved on its entire
native carrier by the actual two chart transitions. -/
theorem injective_mapInTrivializations
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (hj : Function.Injective (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t)) :
    Function.Injective (P.mapInTrivializations eR eA heA t) := by
  intro x y hxy
  apply (eR.coordChangeHomeomorph cR ht.1.1 ht.1.2).injective
  apply hj
  apply Subtype.ext
  apply (cA.coordChangeHomeomorph eA ht.2.2 ht.2.1).injective
  calc
    _ = (P.mapInTrivializations eR eA heA t x).val :=
      (P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x).symm
    _ = (P.mapInTrivializations eR eA heA t y).val := congrArg Subtype.val hxy
    _ = _ := P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht y

/-- The fixed original local expression uses the actual native boundary
diffeomorphism, so its full differential can be computed by the chain rule. -/
theorem mapInTrivializations_eq_local_diffeomorph
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet)) :
    P.mapInTrivializations eR eA heA t =
      (compatibleBoundaryTransitionDiffeomorph cA eA
        (compatibleTrivialization_of_mem hcA) heA ⟨ht.2.2, ht.2.1⟩) ∘
      (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t) ∘ (eR.coordChange cR t) := by
  funext x
  apply Subtype.ext
  rw [Function.comp_apply, Function.comp_apply,
    compatibleBoundaryTransitionDiffeomorph_val]
  exact P.mapInTrivializations_eq_local_val eR eA heA cR hcR cA hcA ht x

/-- The differential of the constructed ribbon map is the actual product
of the boundary transition, original ribbon, and source transition
differentials. All are full native tangent maps, even on the source boundary. -/
theorem mfderiv_mapInTrivializations
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (heR : CompatibleTrivialization I ER eR)
    (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (x : M) :
    mfderiv I 𝓘(ℝ, Model a) (P.mapInTrivializations eR eA heA t) x =
      (mfderiv 𝓘(ℝ, Model a) 𝓘(ℝ, Model a)
        (compatibleBoundaryTransitionDiffeomorph cA eA
          (compatibleTrivialization_of_mem hcA) heA ⟨ht.2.2, ht.2.1⟩)
        (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t (eR.coordChange cR t x))).comp
      ((mfderiv I 𝓘(ℝ, Model a) (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t)
        (eR.coordChange cR t x)).comp
      (mfderiv I I (eR.coordChange cR t) x)) := by
  have hf : ContMDiff I I ∞ (eR.coordChange cR t) := (heR cR hcR).1.contMDiff ht.1
  have hj := (P.smooth ⟨cR, hcR⟩ ⟨cA, hcA⟩).contMDiff_slice
    (IntrinsicBoundary.smoothManifold a A) t ⟨ht.1.2, ht.2.2⟩
  have hg := (compatibleBoundaryTransitionDiffeomorph cA eA
    (compatibleTrivialization_of_mem hcA) heA ⟨ht.2.2, ht.2.1⟩).contMDiff
  rw [P.mapInTrivializations_eq_local_diffeomorph eR eA heA cR hcR cA hcA ht,
    mfderiv_comp x (hg.mdifferentiableAt (by simp))
      ((hj.mdifferentiableAt (by simp)).comp x (hf.mdifferentiableAt (by simp))),
    mfderiv_comp x (hj.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rfl

/-- An original local immersion remains an immersion of the entire
native ribbon in the constructed charts. Bijectivity of both transition
differentials is proved from their actual diffeomorphisms. -/
theorem injective_mfderiv_mapInTrivializations
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (heR : CompatibleTrivialization I ER eR)
    (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA)
    (cR : Trivialization M (π M ER)) (hcR : cR ∈ trivializationAtlas M ER)
    (cA : Trivialization A (π A EA)) (hcA : cA ∈ trivializationAtlas A EA)
    {t : Parameter} (ht : t ∈ (eR.baseSet ∩ cR.baseSet) ∩ (eA.baseSet ∩ cA.baseSet))
    (hj : ∀ y, Function.Injective
      (mfderiv I 𝓘(ℝ, Model a) (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t) y))
    (x : M) :
    Function.Injective (mfderiv I 𝓘(ℝ, Model a) (P.mapInTrivializations eR eA heA t) x) := by
  let f : Diffeomorph I I M M ∞ := {
    __ := (eR.coordChangeHomeomorph cR ht.1.1 ht.1.2).toEquiv
    contMDiff_toFun := (heR cR hcR).1.contMDiff ht.1
    contMDiff_invFun := (heR cR hcR).2.contMDiff ⟨ht.1.2, ht.1.1⟩ }
  have hf : Function.Bijective (mfderiv I I (eR.coordChange cR t) x) :=
    (f.isInvertible_mfderiv (by simp)).bijective
  have hg := compatibleBoundaryTransitionDiffeomorph_bijective_mfderiv cA eA
    (compatibleTrivialization_of_mem hcA) heA ⟨ht.2.2, ht.2.1⟩
    (P.map ⟨cR, hcR⟩ ⟨cA, hcA⟩ t (eR.coordChange cR t x))
  rw [P.mfderiv_mapInTrivializations eR heR eA heA cR hcR cA hcA ht x]
  exact hg.1.comp ((hj _).comp hf.1)

/-- Joint target-valued germs in both compatible charts are produced
from only original local germs, by genuine pre- and postcomposition.
The target extensions take values in the actual intrinsic boundary. -/
theorem smooth_in_compatible_charts
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA)
    (eR : Trivialization M (π M ER)) (heR : CompatibleTrivialization I ER eR)
    (eA : Trivialization A (π A EA))
    (heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA) :
    HasSmoothTargetFamilyOn I (IntrinsicBoundary.smoothManifold a A)
      (eR.baseSet ∩ eA.baseSet) (P.mapInTrivializations eR eA heA) := by
  apply HasSmoothTargetFamilyOn.of_locally
  intro t ht
  let cR := trivializationAt M ER t
  let cA := trivializationAt A EA t
  let B := IntrinsicBoundary.smoothManifold a A
  have hcR : cR ∈ trivializationAtlas M ER := trivialization_mem_atlas _ _ _
  have hcA : cA ∈ trivializationAtlas A EA := trivialization_mem_atlas _ _ _
  have htR : t ∈ cR.baseSet := mem_baseSet_trivializationAt _ _ _
  have htA : t ∈ cA.baseSet := mem_baseSet_trivializationAt _ _ _
  refine ⟨cR.baseSet ∩ cA.baseSet, cR.open_baseSet.inter cA.open_baseSet, ⟨htR, htA⟩, ?_⟩
  have hv := (P.smooth ⟨cR, hcR⟩ ⟨cA, hcA⟩).mono
    (show (eR.baseSet ∩ eA.baseSet) ∩ (cR.baseSet ∩ cA.baseSet) ⊆
      cR.baseSet ∩ cA.baseSet from fun s hs => hs.2)
  have hf := (heR cR hcR).1.hasSmoothFamilyOn.mono
    (show (eR.baseSet ∩ eA.baseSet) ∩ (cR.baseSet ∩ cA.baseSet) ⊆
      eR.baseSet ∩ cR.baseSet from fun s hs => ⟨hs.1.1, hs.2.1⟩)
  have hpre := hv.comp B ((eR.open_baseSet.inter eA.open_baseSet).inter
    (cR.open_baseSet.inter cA.open_baseSet)) hf
    ((continuousOn_coordChange eR cR).mono
      (fun p hp => ⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2⟩))
  have hpost := ((compatibleTransition_boundary_germs cA eA
    (compatibleTrivialization_of_mem hcA) heA).mono
      (show (eR.baseSet ∩ eA.baseSet) ∩ (cR.baseSet ∩ cA.baseSet) ⊆
        cA.baseSet ∩ eA.baseSet from fun s hs => ⟨hs.2.2, hs.1.2⟩)).native_manifold B B
  exact (hpre.postcomp B B hpost).congr (fun s hs x =>
    congrFun (P.mapInTrivializations_eq_local eR eA heA cR hcR cA hcA
      ⟨⟨hs.1.1, hs.2.1⟩, ⟨hs.1.2, hs.2.2⟩⟩).symm x)

/-- Both global charts and the joint ribbon-map germs are conclusions
from the original bundles and local covariant ribbon data. -/
theorem exists_global_charts
    (P : BundleRibbonData (a := a) (M := M) (A := A) I ER EA) :
    ∃ (eR : Trivialization M (π M ER)) (eA : Trivialization A (π A EA)),
      eR.baseSet = univ ∧ eA.baseSet = univ ∧
      CompatibleTrivialization I ER eR ∧
      ∃ heA : CompatibleTrivialization (𝓡∂ (a + 1)) EA eA,
        HasSmoothTargetFamilyOn I (IntrinsicBoundary.smoothManifold a A) univ
          (P.mapInTrivializations eR eA heA) := by
  obtain ⟨eR, hbaseR, heR⟩ := exists_global_smooth_trivialization (I := I) (F := M) (E := ER)
  obtain ⟨eA, hbaseA, heA⟩ :=
    exists_global_smooth_trivialization (I := 𝓡∂ (a + 1)) (F := A) (E := EA)
  exact ⟨eR, eA, hbaseR, hbaseA, heR, heA, by
    simpa only [hbaseR, hbaseA, inter_self] using P.smooth_in_compatible_charts eR heR eA heA⟩

end BundleRibbonData
end FsFltz.Geometry.IntrinsicSmoothBundle
