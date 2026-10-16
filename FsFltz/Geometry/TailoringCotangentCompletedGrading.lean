import FsFltz.Geometry.TailoringCotangentEndpointGradingLegendre
import FsFltz.Geometry.CompletionCompactCompression
import FsFltz.Geometry.TailoringCompletedGradingHitting
import FsFltz.Geometry.MaslovEmbeddingTensor

/-!
# The completed native tensor at the retained cotangent endpoint

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2045–2088.
The full compact marking detects the prescribed native class and hence
grades the actual retained cotangent identification.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- Coefficient removal ends at the literal native tensor. -/
theorem Geometry.MaslovRepresentative.decreasingRankTwoPrimitiveFamily_tensor_one
    {n : ℕ} {M : SmoothManifold (2 * n)} {α : M.Form 1}
    (s : MaslovRepresentative M (M.exteriorDerivative α))
    (hα : M.IsSmoothForm α) (hnd : ∀ x, M.Nondegenerate (M.exteriorDerivative α) x)
    (f : M.Point → ℂ) (hf : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℂ) ∞ f)
    (hπ : ∀ x, 0 ≤ M.planePairing α f x (hnd x)) (K : ℝ) (hK : 0 ≤ K) :
    (s.decreasingRankTwoPrimitiveFamily hα hnd f hf hπ K hK).tensor 1 = s.tensor := by
  funext x
  change rankTwoShearTensor _ _ (K * (1 - 1)) (s.tensor x) = s.tensor x
  ext v
  simp [rankTwoShearTensor, rankTwoShear]

/-- The actual final representative recovers the native tensor through
the retained native embedding and collar inclusion. -/
theorem CompletedHittingRibbonFamily.terminal_tensor_of_native_formula
    {n : ℕ} {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b)
    (f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (α : ℝ → D.extension.Form 1) (τ : ℝ → D.extension.Point → SquaredCanonicalTensor n)
    (hf : ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor α τ t.val)
    (s : MaslovRepresentative D.extension (D.extension.exteriorDerivative (L parameterOne).primitive))
    (hτ : τ 1 = s.tensor)
    (e : D.extension.SmoothEmbedding (lgManifold n))
    (σ : LGSpace n → SquaredCanonicalTensor n)
    (hs : ∀ x, s.tensor x = (σ (e.map x)).compContinuousLinearMap
      (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e.map x))
    (x : (H.ambient.collars parameterOne).localizedDomain.domain.extension.Point)
    (hx : x ∈ (H.ambient.collars parameterOne).localizedDomain.domain.carrier) :
    (H.deformation.maslovFamilyRepresentative f parameterOne).tensor x =
      (σ ((e.comp (H.ambient.collars parameterOne).originalInclusion).map x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
          (e.comp (H.ambient.collars parameterOne).originalInclusion).map x) := by
  let B := H.ambient.collars parameterOne
  rw [H.maslovFamilyRepresentative_tensor_eq_cylindrical_on_carrier f α τ hf
    parameterOne s hτ x hx, (B.cylindricalMaslovOfNative_eq_on_carrier s x hx).2, hs]
  have hd := mfderiv_comp x
    (e.map.contMDiff.mdifferentiableAt (by simp))
    (B.originalInclusion.map.contMDiff.mdifferentiableAt (by simp))
  have hid := B.mfderiv_originalInclusion x
  change mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
    (e.map ∘ B.originalInclusion.map) x = _ at hd
  rw [hid] at hd
  ext v
  change σ (e.map x.val.val) (fun i => mfderiv _ _ e.map x.val.val (v i)) =
    σ (e.map x.val.val) (fun i => mfderiv _ _ (e.map ∘ B.originalInclusion.map) x (v i))
  rw [hd]
  rfl

/-- The coefficient-removal family has the literal prescribed logarithmic
tensor on the entire terminal compact domain. -/
theorem CompletedHittingRibbonFamily.hitting_terminal_tensor
    {n : ℕ} {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b)
    (I : ToricInput n) {φ : RealSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (β K : ℝ) (hK : 0 ≤ K)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 1) y (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y))
    (ι : D.extension.SmoothEmbedding (lgManifold n))
    (hL : ∀ t : Parameter, (L t).primitive = D.extension.pullback (lgManifold n) ι.map
      (hittingNativePrimitiveFamily I φ β K t.val))
    (f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (hf : ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor
      (fun u => D.extension.pullback (lgManifold n) ι.map (hittingNativePrimitiveFamily I φ β K u))
      (hittingNativeDomainMaslovFamily ι I hφ hc hlower β hπ K hK).tensor t.val)
    (x : (H.ambient.collars parameterOne).localizedDomain.domain.extension.Point)
    (hx : x ∈ (H.ambient.collars parameterOne).localizedDomain.domain.carrier) :
    (H.deformation.maslovFamilyRepresentative f parameterOne).tensor x =
      (logarithmicSquaredVolumeTensor n
        ((ι.comp (H.ambient.collars parameterOne).originalInclusion).map x)).compContinuousLinearMap
        (fun _ => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n))
          (ι.comp (H.ambient.collars parameterOne).originalInclusion).map x) := by
  let sN := hittingNativeMaslovFamily I hφ hc hlower β hπ K hK
  let sD := hittingNativeDomainMaslovFamily ι I hφ hc hlower β hπ K hK
  have hcomp : IsCompatibleAlmostComplex D.extension
      (D.extension.exteriorDerivative (L parameterOne).primitive) (sD.J 1) := by
    rw [hL parameterOne]
    exact sD.compatible 1 parameterOne.property
  let s : MaslovRepresentative D.extension (D.extension.exteriorDerivative (L parameterOne).primitive) :=
    { sD.representative parameterOne with compatible := hcomp }
  apply H.terminal_tensor_of_native_formula f _ sD.tensor hf s rfl ι
    (logarithmicSquaredVolumeTensor n) _ x hx
  intro y
  change sD.tensor 1 y = _
  apply Eq.trans (sN.pullbackPrimitiveEmbedding_tensor_apply
    (fun _ ht => (isSmoothFormFamily_hittingNativePrimitive I hφ β K).slice ht) ι 1 y)
  have hN : sN.tensor 1 = logarithmicSquaredVolumeTensor n :=
    (potentialMaslovRepresentative hφ hc hlower).decreasingRankTwoPrimitiveFamily_tensor_one
      (isSmoothForm_lambdaPotentialForm hφ)
      (nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower)
      (tailoringFamily I β 1) (contMDiff_tailoringFamily_lgManifold I β 1) hπ K hK
  change (sN.tensor 1 (ι.map y)).compContinuousLinearMap _ = _
  rw [hN]

/-- The full compact tensor formula, including the boundary derivatives,
determines the native logarithmic class on the actual cylindrical completion. -/
theorem CompletedHittingRibbonFamily.completed_homotopic_markedNative
    {n : ℕ} {φEnd φ : RealSpace n → ℝ}
    (Dφ : RetainedLegendrePotential φEnd φ) (I : ToricInput n)
    {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b)
    (e : (H.ambient.collars parameterOne).localizedDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (q : H.deformation.target.ambientManifold.SmoothEquiv (lgManifold n))
    (hq : H.deformation.target.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
      H.deformation.target.ambientCompletion.ambient.primitive)
    (r : H.deformation.target.Maslov)
    (hcompact : ∀ x ∈ (H.ambient.collars parameterOne).localizedDomain.domain.carrier,
      q x = e.map x)
    (htensor : ∀ x ∈ (H.ambient.collars parameterOne).localizedDomain.domain.carrier, ∀ v,
      r.tensor x v =
        (Dφ.nativeMaslov I).tensor (e.map x)
          (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e.map x (v i))) :
    MaslovHomotopic r (Dφ.markedNativeMaslov I H.deformation.target q hq) := by
  apply (H.ambient.collars parameterOne).maslovHomotopic_of_eq_on_carrier
  intro x hx
  have hd := (H.ambient.collars parameterOne).localizedDomain.domain.mfderiv_eq_of_eqOn_carrier (lgManifold n)
    (fun _ _ => q.contMDiff.mdifferentiableAt (by simp))
    (fun _ _ => e.map.contMDiff.mdifferentiableAt (by simp))
    (fun z hz => hcompact z hz) x hx
  ext v
  change (Dφ.nativeMaslov I).tensor (q x)
    (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) q x (v i)) = _
  rw [hd, hcompact x hx]
  exact (htensor x hx v).symm

/-- The actual completed endpoint datum grades the retained cotangent
identification when its compact tensor is the native logarithmic tensor. -/
theorem CompletedHittingRibbonFamily.graded_cotangentIdentification_of_compact_tensor
    {n : ℕ} {φEnd φ : RealSpace n → ℝ}
    (Dφ : RetainedLegendrePotential φEnd φ) (I : ToricInput n)
    {D : CompactDomain (2 * n)} {F : LiouvilleDomain (2 * n - 2)}
    {L : Parameter → LiouvilleStructure D}
    {j : Parameter → F.domain.extension.SmoothEmbedding D.boundary}
    {b : Parameter → D.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily D F L j b)
    (e : (H.ambient.collars parameterOne).localizedDomain.domain.extension.SmoothEmbedding (lgManifold n))
    (q : H.deformation.target.ambientManifold.SmoothEquiv (lgManifold n))
    (hq : H.deformation.target.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
      H.deformation.target.ambientCompletion.ambient.primitive)
    (r : H.deformation.target.Maslov)
    (hcompact : ∀ x ∈ (H.ambient.collars parameterOne).localizedDomain.domain.carrier,
      q x = e.map x)
    (htensor : ∀ x ∈ (H.ambient.collars parameterOne).localizedDomain.domain.carrier, ∀ v,
      r.tensor x v =
        (Dφ.nativeMaslov I).tensor (e.map x)
          (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) e.map x (v i)))
    (E : CotangentPairData n) (C : CompletionIdentification H.deformation.target E.pair)
    (hmap : ∀ y, E.marking (C.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) :
    Nonempty (GradedCompletionIdentification C r E.verticalMaslov) := by
  have he := H.completed_homotopic_markedNative Dφ I e q hq r hcompact htensor
  have hgrade := Dφ.graded_cotangentIdentification I H.deformation.target q hq E C hmap
  exact (C.gradedLift_iff_class_eq r E.verticalMaslov).mpr
    ((Quot.sound he).trans
      ((C.gradedLift_iff_class_eq _ E.verticalMaslov).mp hgrade))

/-- The actual completed coefficient-removal datum reaches the prescribed
vertical datum on the retained endpoint with literal full FLTZ core. -/
theorem CompletedHittingRibbonFamily.exists_graded_cotangentEndpoint_of_hitting_family
    {n : ℕ} {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
    (Dφ : RetainedLegendrePotential φEnd φ)
    (hstrong : IsStronglyCompatibleEndPotential I φEnd)
    {A : ℝ} (hA : 0 < A)
    (hlevelEq : {y : LGSpace n | φ y.1 = A} = {y : LGSpace n | φEnd y.1 = A})
    (hgradient : ∀ u, φ u = A → coordinateGradient φ u = coordinateGradient φEnd u)
    (hout : ∀ y : LGSpace n, A ≤ φ y.1 →
      0 < (lgManifold n).scalarDerivative (fun z => φ z.1) y
        ((lgManifold n).liouvilleVector (lambdaPotentialForm φ) y))
    {Q : PairDeformation n}
    {J : ∀ t, (Q.pair t).ambientDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {α : Parameter → (lgManifold n).Form 1}
    (O : OuterAmbientInclusionMarkingFamily Q J (fun y => φ y.1 - A) α)
    (hD : O.domain.carrier.Nonempty)
    (hboundary : range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map =
      {y | φ y.1 = A})
    {F : LiouvilleDomain (2 * n - 2)} {L : Parameter → LiouvilleStructure O.domain}
    {j : Parameter → F.domain.extension.SmoothEmbedding O.domain.boundary}
    {b : Parameter → O.domain.boundary.Point → ℝ}
    (H : CompletedHittingRibbonFamily O.domain F L j b)
    (β K : ℝ) (hK : 0 ≤ K)
    (hπ : ∀ y, 0 ≤ (lgManifold n).planePairing (lambdaPotentialForm φ)
      (tailoringFamily I β 1) y
        (nondegenerate_lambdaPotentialForm_of_lowerBound Dφ.smooth Dφ.lower_pos Dφ.hessian_lower y))
    (hL : ∀ t : Parameter, (L t).primitive = O.domain.extension.pullback (lgManifold n)
      O.nativeEmbedding.map (hittingNativePrimitiveFamily I φ β K t.val))
    (f : MaslovFamily H.deformation.source.ambientManifold H.deformation.completedSymplecticExtension)
    (hf : ∀ t : Parameter, f.tensor t.val = H.ambient.completedNativeTensor
      (fun u => O.domain.extension.pullback (lgManifold n) O.nativeEmbedding.map
        (hittingNativePrimitiveFamily I φ β K u))
      (hittingNativeDomainMaslovFamily O.nativeEmbedding I Dφ.smooth Dφ.lower_pos
        Dφ.hessian_lower β hπ K hK).tensor t.val)
    (hcore : (O.nativeEmbedding.comp O.domain.boundaryInclusion).map '' H.deformation.target.embeddedCore =
      tailoringLegendreConic I φEnd ∩ range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map) :
    ∃ E : CotangentPairData n, ∃ C : CompletionIdentification H.deformation.target E.pair,
      E.embeddedCore = fltzLink I ∧
      Nonempty (GradedCompletionIdentification C
        (H.deformation.maslovFamilyRepresentative f parameterOne) E.verticalMaslov) := by
  have hzero : (L parameterOne).primitive = O.domain.extension.pullback (lgManifold n)
      O.nativeEmbedding.map (lambdaPotentialForm φ) := by
    simpa [hittingNativePrimitiveFamily, parameterOne, SmoothManifold.rankTwoPrimitive] using hL parameterOne
  obtain ⟨q, hq, hc, E, C, hmap, _hr, _hcompletion, _hid, _hscale, _hb, _hw, hfltz⟩ :=
    H.exists_retained_cotangentEndpoint_with_compact Dφ hstrong hA hlevelEq hgradient hout
      O hD hboundary hzero hcore
  refine ⟨E, C, hfltz, ?_⟩
  apply H.graded_cotangentIdentification_of_compact_tensor Dφ I
    (O.nativeEmbedding.comp (H.ambient.collars parameterOne).originalInclusion) q hq
    (H.deformation.maslovFamilyRepresentative f parameterOne) hc _ E C hmap
  intro x hx v
  exact congrArg (fun T : SquaredCanonicalTensor n => T v)
    (H.hitting_terminal_tensor I Dφ.smooth Dφ.lower_pos Dφ.hessian_lower β K hK hπ
      O.nativeEmbedding hL f hf x hx)

end FsFltz
