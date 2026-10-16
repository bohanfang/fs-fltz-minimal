import FsFltz.Geometry.TailoringStrictJunctionGradingNative
import FsFltz.Geometry.TailoringCompletedGradingHitting
import FsFltz.Geometry.MaslovEmbeddingTensor

/-!
# Actual compact tensor alignment at the retained incoming junction

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1891–1919,
`lem:grading`, lines 2025–2045, and `sec:assembly`, lines 2159–2233.
The two constructed completed families are compared through their actual
compact native square, with no completed grading match assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

namespace OuterAmbientInclusionMarkingFamily

/-- The retained outer marking and its compact square recover the actual
native tensor on the full compact slice, including its boundary frames. -/
theorem maslovFamilyRepresentative_tensor_compact_native
    {n : ℕ} {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {ρ : LGSpace n → ℝ} {αN : ℝ → (lgManifold n).Form 1}
    (R : OuterAmbientInclusionMarkingFamily Q J ρ (fun t => αN t.val))
    (hαN : (lgManifold n).IsSmoothFormFamily αN)
    (sN : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (αN t)))
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (hf : ∀ t : Parameter, f.tensor t.val = pullbackSquaredTensor Q.source.ambientManifold
      (R.family.collars parameterZero).localizedDomain.domain.extension (R.zeroOuterComparison t)
        (R.family.completedNativeTensor R.domainPrimitiveFamily
          (R.domainMaslovFamily hαN sN).tensor t.val))
    (t : Parameter)
    (hcompact : ∀ x : (Q.pair t).ambientDomain.domain.Point,
      R.inclusion t x ∈ (R.family.collars t).localizedDomain.domain.carrier)
    (x : (Q.pair t).ambientDomain.domain.extension.Point)
    (hx : x ∈ (Q.pair t).ambientDomain.domain.carrier)
    (v : Fin n ⊕ Fin n → Model (2 * n)) :
    (Q.maslovFamilyRepresentative f t).tensor ((Q.pair t).ambientCompletion.inclusion.map x)
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (Q.pair t).ambientCompletion.inclusion.map x (v i)) =
      sN.tensor t.val ((J t).map x)
        (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (J t).map x (v i)) := by
  let C := R.family.collars t
  let D := (Q.pair t).ambientDomain.domain
  let e := (R.marking t).equiv
  let sD := R.domainMaslovFamily hαN sN
  have hcomp : IsCompatibleAlmostComplex R.domain.extension
      (R.domain.extension.exteriorDerivative (R.liouville t).primitive) (sD.J t.val) := by
    rw [R.native_primitive t]
    exact sD.compatible t.val t.property
  let s : MaslovRepresentative R.domain.extension
      (R.domain.extension.exteriorDerivative (R.liouville t).primitive) :=
    { sD.representative t with compatible := hcomp }
  have hmem : e ((Q.pair t).ambientCompletion.inclusion.map x) ∈ C.localizedDomain.domain.carrier := by
    rw [(R.marking t).inclusion ⟨x, hx⟩]
    exact hcompact ⟨x, hx⟩
  have ht := R.maslovFamilyRepresentative_tensor_eq_cylindrical_of_marked_mem_carrier
    f R.domainPrimitiveFamily sD.tensor hf t s rfl _ hmem
  let z := e ((Q.pair t).ambientCompletion.inclusion.map x)
  have hnative := (C.cylindricalMaslovOfNative_eq_on_carrier s z hmem).2
  have hs := sN.pullbackPrimitiveEmbedding_tensor_apply
    (fun _ ht => hαN.slice ht) R.nativeEmbedding t.val z.val.val
  have hd₀ := mfderiv_comp x (e.mdifferentiable (by simp) _)
    ((Q.pair t).ambientCompletion.inclusion.map.contMDiff.mdifferentiableAt (by simp))
  have hd₁ := mfderiv_comp x
    (C.originalInclusion.map.contMDiff.mdifferentiableAt (by simp))
    ((e.contMDiff.comp (Q.pair t).ambientCompletion.inclusion.map.contMDiff).mdifferentiableAt (by simp))
  have hd₂ := mfderiv_comp x
    (R.nativeEmbedding.map.contMDiff.mdifferentiableAt (by simp))
    ((C.originalInclusion.map.contMDiff.comp
      (e.contMDiff.comp (Q.pair t).ambientCompletion.inclusion.map.contMDiff)).mdifferentiableAt (by simp))
  let F : D.extension.Point → (lgManifold n).Point :=
    R.nativeEmbedding.map ∘ C.originalInclusion.map ∘ e ∘ (Q.pair t).ambientCompletion.inclusion.map
  have hF : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) ∞ F :=
    R.nativeEmbedding.map.contMDiff.comp (C.originalInclusion.map.contMDiff.comp
      (e.contMDiff.comp (Q.pair t).ambientCompletion.inclusion.map.contMDiff))
  have hsquare : ∀ y ∈ D.carrier, F y = (J t).map y := by
    intro y hy
    change R.nativeEmbedding.map (C.originalInclusion.map
      (e ((Q.pair t).ambientCompletion.inclusion.map y))) = _
    rw [(R.marking t).inclusion ⟨y, hy⟩]
    exact R.compact_square t ⟨y, hy⟩
  have hd := D.mfderiv_eq_of_eqOn_carrier (lgManifold n)
    (fun _ _ => hF.mdifferentiableAt (by simp))
    (fun _ _ => (J t).map.contMDiff.mdifferentiableAt (by simp)) hsquare x hx
  have hdF := hd₂
  rw [hd₁, hd₀, C.mfderiv_originalInclusion] at hdF
  have hframe (w : Model (2 * n)) :
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) R.nativeEmbedding.map z.val.val
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e
          ((Q.pair t).ambientCompletion.inclusion.map x)
          (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
            (Q.pair t).ambientCompletion.inclusion.map x w)) =
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) (J t).map x w := by
    exact (congrArg (fun A => A w) hdF).symm.trans (congrArg (fun A => A w) hd)
  have hpoint : R.nativeEmbedding.map z.val.val = (J t).map x := hsquare x hx
  change _ = _
  rw [ht]
  change (C.cylindricalMaslovOfNative s).tensor z
    (fun i => mfderiv _ _ e ((Q.pair t).ambientCompletion.inclusion.map x)
      (mfderiv _ _ (Q.pair t).ambientCompletion.inclusion.map x (v i))) = _
  rw [hnative]
  change sD.tensor t.val z.val.val _ = _
  refine (congrArg (fun T : SquaredCanonicalTensor n => T
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e
      ((Q.pair t).ambientCompletion.inclusion.map x)
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
        (Q.pair t).ambientCompletion.inclusion.map x (v i)))) hs).trans ?_
  change sN.tensor t.val (R.nativeEmbedding.map z.val.val)
    (fun i => mfderiv _ _ R.nativeEmbedding.map z.val.val
      (mfderiv _ _ e ((Q.pair t).ambientCompletion.inclusion.map x)
        (mfderiv _ _ (Q.pair t).ambientCompletion.inclusion.map x (v i)))) = _
  exact (congrArg (fun y => sN.tensor t.val y
    (fun i => mfderiv _ _ R.nativeEmbedding.map z.val.val
      (mfderiv _ _ e ((Q.pair t).ambientCompletion.inclusion.map x)
        (mfderiv _ _ (Q.pair t).ambientCompletion.inclusion.map x (v i))))) hpoint).trans
      (congrArg (sN.tensor t.val ((J t).map x)) (funext (fun i => hframe (v i))))

end OuterAmbientInclusionMarkingFamily

namespace CompletedHittingRibbonFamily

/-- Every constructed completed hitting slice has its actual native tensor
on the localized compact carrier, through the same native embedding. -/
theorem maslovFamilyRepresentative_tensor_native
    {n : ℕ} {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b)
    {αN : ℝ → (lgManifold n).Form 1}
    (hαN : (lgManifold n).IsSmoothFormFamily αN)
    (sN : MaslovFamily (lgManifold n) (fun t => (lgManifold n).exteriorDerivative (αN t)))
    (e : D.extension.SmoothEmbedding (lgManifold n))
    (hL : ∀ t : Parameter, (L t).primitive = D.extension.pullback (lgManifold n) e.map (αN t.val))
    (f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (hf : ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor
      (fun u => D.extension.pullback (lgManifold n) e.map (αN u))
      (sN.pullbackPrimitiveEmbedding (fun _ ht => hαN.slice ht) e).tensor t.val)
    (t : Parameter) (x : (H.ambient.collars t).localizedDomain.domain.extension.Point)
    (hx : x ∈ (H.ambient.collars t).localizedDomain.domain.carrier) :
    (H.deformation.maslovFamilyRepresentative f t).tensor x =
      (sN.tensor t.val ((e.comp (H.ambient.collars t).originalInclusion).map x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
          (e.comp (H.ambient.collars t).originalInclusion).map x) := by
  let C := H.ambient.collars t
  let sD := sN.pullbackPrimitiveEmbedding (fun _ ht => hαN.slice ht) e
  have hcomp : IsCompatibleAlmostComplex D.extension
      (D.extension.exteriorDerivative (L t).primitive) (sD.J t.val) := by
    rw [hL t]
    exact sD.compatible t.val t.property
  let s : MaslovRepresentative D.extension (D.extension.exteriorDerivative (L t).primitive) :=
    { sD.representative t with compatible := hcomp }
  have ht := H.maslovFamilyRepresentative_tensor_eq_cylindrical_on_carrier f _ sD.tensor hf t s rfl x hx
  have hs := sN.pullbackPrimitiveEmbedding_tensor_apply (fun _ ht => hαN.slice ht) e t.val x.val.val
  have he := ht.trans ((C.cylindricalMaslovOfNative_eq_on_carrier s x hx).2.trans hs)
  refine he.trans ?_
  have hd := mfderiv_comp x (e.map.contMDiff.mdifferentiableAt (by simp))
    (C.originalInclusion.map.contMDiff.mdifferentiableAt (by simp))
  rw [C.mfderiv_originalInclusion] at hd
  ext v
  exact congrArg (sN.tensor t.val (e.map x.val.val))
    (funext (fun i => (congrArg (fun A => A (v i)) hd).symm))

end CompletedHittingRibbonFamily

local instance strictJunctionAlignmentLGCharts {n : ℕ} : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts
local instance strictJunctionAlignmentLGSmooth {n : ℕ} : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) :=
  (lgManifold n).smooth

namespace PotentialTailoringMarkedPrefix

set_option maxHeartbeats 500000 in
/-- The exact completed tailoring endpoint is homotopic to the exact
completed hitting source pulled through their retained incoming marking.
Both section formulas come from the actual native families; their equality
is proved from the common potential and the adjacent coefficient values. -/
theorem completed_source_homotopic
    {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (hK : 0 ≤ K)
    (S : IntrinsicShrinkingData P.tailoring.deformation.target)
    {L : Parameter → LiouvilleStructure P.tailoring_ambient_marking.domain}
    {j : Parameter → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding
      P.tailoring_ambient_marking.domain.boundary}
    {b : Parameter → P.tailoring_ambient_marking.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily P.tailoring_ambient_marking.domain
      (S.pair parameterOne).ribbonDomain L j b)
    (hL : ∀ t : Parameter, (L t).primitive =
      P.tailoring_ambient_marking.domain.extension.pullback (lgManifold n)
        P.tailoring_ambient_marking.nativeEmbedding.map (hittingNativePrimitiveFamily I φ β K t.val))
    (fT : MaslovFamily P.tailoring.deformation.source.ambientManifold
      P.tailoring.deformation.completedSymplecticExtension)
    (hfT : ∀ t : Parameter, fT.tensor t.val = pullbackSquaredTensor
      P.tailoring.deformation.source.ambientManifold
      (P.tailoring_ambient_marking.family.collars parameterZero).localizedDomain.domain.extension
      (P.tailoring_ambient_marking.zeroOuterComparison t)
      (P.tailoring_ambient_marking.family.completedNativeTensor
        (P.tailoring_ambient_marking.domainPrimitiveFamily (αN := fun u =>
          (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β u) K))
        (P.tailoring_ambient_marking.domainMaslovFamily
          (isSmoothFormFamily_tailoringPrimitive I β K hφ)
          (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)).tensor t.val))
    (fH : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (hfH : ∀ t : Parameter, fH.tensor t.val = H.ambient.completedNativeTensor
      (fun u => P.tailoring_ambient_marking.domain.extension.pullback (lgManifold n)
        P.tailoring_ambient_marking.nativeEmbedding.map (hittingNativePrimitiveFamily I φ β K u))
      (hittingNativeDomainMaslovFamily P.tailoring_ambient_marking.nativeEmbedding I hφ hc hlower β
        (hπ 1 parameterOne.property) K hK).tensor t.val)
    (i : (S.pair parameterOne).ambientDomain.domain.Point →
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient.manifold.Point)
    (q : InclusionMarking (S.pair parameterOne).ambientCompletion
      (H.ambient.collars parameterZero).cylindricalCompletion.ambient i)
    (hi : ∀ x : (S.pair parameterOne).ambientDomain.domain.Point,
      (P.tailoring_ambient_marking.nativeEmbedding.comp
        (H.ambient.collars parameterZero).originalInclusion).map (i x) =
          (P.tailoring.embedding parameterOne).map x.val) :
    MaslovHomotopic
      (P.tailoring.deformation.maslovFamilyRepresentative fT parameterOne)
      ((H.deformation.maslovFamilyRepresentative fH parameterZero).pullbackTo q.equiv
        (by
          exact ((S.pair parameterOne).ambientManifold.exteriorDerivative_pullback
            H.deformation.source.ambientManifold q.equiv.toContMDiffMap
            H.deformation.source.ambientCompletion.ambient.primitive
            H.deformation.source.ambientCompletion.ambient.smooth_primitive).symm.trans
              (congrArg (S.pair parameterOne).ambientManifold.exteriorDerivative q.primitive))) := by
  let O := P.tailoring_ambient_marking
  let sT := tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK
  let sH := hittingNativeMaslovFamily I hφ hc hlower β (hπ 1 parameterOne.property) K hK
  let C := H.ambient.collars parameterZero
  let source := P.tailoring.deformation.maslovFamilyRepresentative fT parameterOne
  let target := H.deformation.maslovFamilyRepresentative fH parameterZero
  let g := O.nativeEmbedding.comp C.originalInclusion
  have hnative : sT.tensor 1 = sH.tensor 0 :=
    tailoringNativeMaslovFamily_tensor_one_eq_decreasing_zero I hφ hc hlower β hπ K hK
  apply (S.pair parameterOne).ambientCompletion.maslovHomotopic_of_compact_native_square
    (P.tailoring.ambient_nonempty parameterOne) H.deformation.source.ambientManifold
    (lgManifold n) q.equiv _ (P.tailoring.embedding parameterOne).map g.map (sT.tensor 1) source target
  · intro x hx
    exact (congrArg g.map (q.inclusion ⟨x, hx⟩)).trans (hi ⟨x, hx⟩)
  · intro x hx v
    exact O.maslovFamilyRepresentative_tensor_compact_native
      (αN := fun u => (lgManifold n).rankTwoPrimitive
        (lambdaPotentialForm φ) (tailoringFamily I β u) K)
      (isSmoothFormFamily_tailoringPrimitive I β K hφ) sT fT hfT parameterOne
      (P.hitting_marking_mem_carrier (L := fun _ => O.liouville parameterOne)
        (O.family.collars parameterOne) (O.inclusion parameterOne) (O.compact_square parameterOne))
      x hx v
  · intro x hx v
    have hmem : q.equiv ((S.pair parameterOne).ambientCompletion.inclusion.map x) ∈
        C.localizedDomain.domain.carrier := by
      exact (congrArg (fun z => z ∈ C.localizedDomain.domain.carrier)
        (q.inclusion ⟨x, hx⟩)).mpr (P.hitting_marking_mem_carrier C i hi ⟨x, hx⟩)
    have ht := H.maslovFamilyRepresentative_tensor_native
      (isSmoothFormFamily_hittingNativePrimitive I hφ β K) sH O.nativeEmbedding hL fH hfH
      parameterZero _ hmem
    have hv := congrArg (fun T : SquaredCanonicalTensor n => T v) ht
    change target.tensor _ v = sT.tensor 1 (g.map _) (fun i => mfderiv _ _ g.map _ (v i))
    refine hv.trans ?_
    exact congrArg (fun T : (lgManifold n).Point → SquaredCanonicalTensor n =>
      T (g.map (q.equiv ((S.pair parameterOne).ambientCompletion.inclusion.map x)))
        (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) g.map
          (q.equiv ((S.pair parameterOne).ambientCompletion.inclusion.map x)) (v i))) hnative.symm



/-- The actual retained incoming three-arrow junction is graded from the
prescribed endpoint of the actual tailoring family to the actual endpoint
of the actual hitting family. The source match is proved from the two
native formulas and their retained full compact square. -/
theorem exists_graded_strictJunction_of_completed_native_families
    {n : ℕ} {I : ToricInput n} {φ : RealSpace n → ℝ}
    {β Cplus Aminus K : ℝ} {m : RoundingChoice}
    (P : PotentialTailoringMarkedPrefix I φ β Cplus Aminus K m)
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hπ : ∀ s ∈ parameterInterval, ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β s) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (hK : 0 ≤ K)
    (S : IntrinsicShrinkingData P.tailoring.deformation.target)
    {L : Parameter → LiouvilleStructure P.tailoring_ambient_marking.domain}
    {j : Parameter → (S.pair parameterOne).ribbonDomain.domain.extension.SmoothEmbedding
      P.tailoring_ambient_marking.domain.boundary}
    {b : Parameter → P.tailoring_ambient_marking.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily P.tailoring_ambient_marking.domain
      (S.pair parameterOne).ribbonDomain L j b)
    (hL : ∀ t : Parameter, (L t).primitive =
      P.tailoring_ambient_marking.domain.extension.pullback (lgManifold n)
        P.tailoring_ambient_marking.nativeEmbedding.map (hittingNativePrimitiveFamily I φ β K t.val))
    (hboundary : range (P.tailoring_ambient_marking.nativeEmbedding.comp
      P.tailoring_ambient_marking.domain.boundaryInclusion).map =
      {y | φ y.1 = Cplus ^ 2 * β ^ 2 / 2})
    (hnd : ∀ y : LGSpace n, (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative
      ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) y)
    (hout : ∀ y : LGSpace n, φ y.1 = Cplus ^ 2 * β ^ 2 / 2 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K) y))
    (G : Flow ℝ (ℝ × LGSpace n))
    (hG : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (ℝ × LGSpace n) => G p.1 p.2))
    (hnative : ∀ y t, φ (G t (K, y)).2.1 ≤ Cplus ^ 2 * β ^ 2 / 2 →
      IsMIntegralCurveAt (fun s => (G s (K, y)).2)
        ((lgManifold n).liouvilleVector ((lgManifold n).rankTwoPrimitive
          (lambdaPotentialForm φ) (tailoringFamily I β 1) K)) t)
    (τ : (S.pair parameterOne).ribbonDomain.domain.extension.Point → ℝ)
    (htime : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier, 0 < τ x)
    (hhit : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      (G (τ x) (K, (P.tailoring.ribbon_marking parameterOne).embedding.map
        ((S.fiberEmbedding (P.tailoring.ribbon_marking parameterOne) parameterOne).map x))).2 =
      (P.tailoring_ambient_marking.nativeEmbedding.comp
        P.tailoring_ambient_marking.domain.boundaryInclusion).map ((j parameterZero).map x))
    (hwitness : ∀ x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier,
      b parameterZero ((j parameterZero).map x) = Real.exp (-τ x))
    (fT : MaslovFamily P.tailoring.deformation.source.ambientManifold
      P.tailoring.deformation.completedSymplecticExtension)
    (hfT : ∀ t : Parameter, fT.tensor t.val = pullbackSquaredTensor
      P.tailoring.deformation.source.ambientManifold
      (P.tailoring_ambient_marking.family.collars parameterZero).localizedDomain.domain.extension
      (P.tailoring_ambient_marking.zeroOuterComparison t)
      (P.tailoring_ambient_marking.family.completedNativeTensor
        (P.tailoring_ambient_marking.domainPrimitiveFamily (αN := fun u =>
          (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β u) K))
        (P.tailoring_ambient_marking.domainMaslovFamily
          (isSmoothFormFamily_tailoringPrimitive I β K hφ)
          (tailoringNativeMaslovFamily I hφ hc hlower β hπ K hK)).tensor t.val))
    (fH : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (hfH : ∀ t : Parameter, fH.tensor t.val = H.ambient.completedNativeTensor
      (fun u => P.tailoring_ambient_marking.domain.extension.pullback (lgManifold n)
        P.tailoring_ambient_marking.nativeEmbedding.map (hittingNativePrimitiveFamily I φ β K u))
      (hittingNativeDomainMaslovFamily P.tailoring_ambient_marking.nativeEmbedding I hφ hc hlower β
        (hπ 1 parameterOne.property) K hK).tensor t.val)
    (gH : GradedPairDeformation H.deformation
      (H.deformation.maslovFamilyRepresentative fH parameterZero)
      (H.deformation.maslovFamilyRepresentative fH parameterOne)) :
    ∃ J : StrictHittingJunction (S.pair parameterOne) H.deformation,
      Nonempty (GradedComparisonChain (S.pair parameterOne) J.chain
        (P.tailoring.deformation.maslovFamilyRepresentative fT parameterOne)
        (H.deformation.maslovFamilyRepresentative fH parameterOne)) := by
  have hL₀ : (L parameterZero).primitive = P.tailoring_ambient_marking.domain.extension.pullback
      (lgManifold n) P.tailoring_ambient_marking.nativeEmbedding.map
        ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 1) K) := by
    simpa only [hittingNativePrimitiveFamily, parameterZero, sub_zero, mul_one] using hL parameterZero
  obtain ⟨i, q, hi, J, datum, _, htensor, ⟨gJ⟩⟩ :=
    P.exists_graded_strictJunction_into_retained_hitting hφ S H hL₀ hboundary hnd hout
      G hG hnative τ htime hhit hwitness
      (H.deformation.maslovFamilyRepresentative fH parameterZero)
      (H.deformation.maslovFamilyRepresentative fH parameterOne) gH
  have hs := P.completed_source_homotopic hφ hc hlower hπ hK S H hL fT hfT fH hfH i q hi
  have hη : (S.pair parameterOne).ambientManifold.pullback H.deformation.source.ambientManifold
      q.equiv H.deformation.source.ambientSymplecticForm = (S.pair parameterOne).ambientSymplecticForm :=
    ((S.pair parameterOne).ambientManifold.exteriorDerivative_pullback
      H.deformation.source.ambientManifold q.equiv.toContMDiffMap
      H.deformation.source.ambientCompletion.ambient.primitive
      H.deformation.source.ambientCompletion.ambient.smooth_primitive).symm.trans
        (congrArg (S.pair parameterOne).ambientManifold.exteriorDerivative q.primitive)
  let r := (H.deformation.maslovFamilyRepresentative fH parameterZero).pullbackTo q.equiv hη
  have hr : MaslovHomotopic r datum := r.homotopic_of_tensor_eq datum htensor.symm
  exact ⟨J, J.gradedChain_of_source_homotopic gJ (hs.trans hr)⟩

end PotentialTailoringMarkedPrefix
end FsFltz
