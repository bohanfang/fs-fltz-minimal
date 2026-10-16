import FsFltz.Geometry.TailoringCotangentEndpointGrading

/-!
# The actual Legendre grading bridge for the retained potential

Source: `geometric-part-fsf-proof.tex`, `lem:grading`, lines 2075–2088.
The compatible-structure normalization reduces the endpoint to a positive
real squared determinant ratio, without replacing the selected potential.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff BigOperators
open Set

namespace FsFltz
open Geometry Geometry.SmoothManifold
variable {n : ℕ} {φEnd φ : RealSpace n → ℝ}

/-- The same selected Legendre derivative has the actual Hessian and
angular-identity blocks in the quotient coframes. -/
theorem RetainedLegendrePotential.legendre_derivative_coframe
    (D : RetainedLegendrePotential φEnd φ) (x q : TangentCoordinates n) :
    cotangentTangentCoframe (D.legendre (lgCover x))
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) D.legendre
        (lgCover x) (lgCoverTangent x q)) =
      (fderiv ℝ (coordinateGradient φ) x.1 q.1, q.2) := by
  have he : (D.legendre : LGSpace n → Cotangent n) = legendreMap (coordinateGradient φ) := by
    funext y
    simp [RetainedLegendrePotential.legendre, legendreMap, D.gradient_eq]
  rw [he, legendreMap_lgCoverTangent (contDiff_coordinateGradient D.smooth) x q]
  exact cotangentTangentCoframe_cotangentCover (x.2, coordinateGradient φ x.1)
    (q.2, fderiv ℝ (coordinateGradient φ) x.1 q.1)

/-- Normalizing the Legendre-pulled structure to the logarithmic structure
has the real block $(I+H)/2$ in both canonical coframe components. -/
theorem RetainedLegendrePotential.normalization_derivative_coframe
    (D : RetainedLegendrePotential φEnd φ) (x q : TangentCoordinates n) :
    cotangentTangentCoframe (D.legendre (lgCover x))
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) D.legendre
        (lgCover x)
        (compatibleComplexTransport (D.legendreMaslov.J (lgCover x))
          (logarithmicAlmostComplexField n (lgCover x)) (lgCoverTangent x q))) =
      ((2 : ℝ)⁻¹ • (fderiv ℝ (coordinateGradient φ) x.1 q.1 + q.1),
       (2 : ℝ)⁻¹ • (q.2 + fderiv ℝ (coordinateGradient φ) x.1 q.2)) := by
  let A := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) D.legendre (lgCover x)
  have hi (v : (lgManifold n).Tangent (lgCover x)) :
      A (D.legendreMaslov.J (lgCover x) v) =
        cotangentAlmostComplexField n (D.legendre (lgCover x)) (A v) :=
    pullbackAlmostComplex_intertwines (lgManifold n) (cotangentManifold n)
      D.legendre (cotangentAlmostComplexField n) (lgCover x) v
  change cotangentTangentCoframe _
    (A ((2 : ℝ)⁻¹ • (lgCoverTangent x q - D.legendreMaslov.J (lgCover x)
      (logarithmicAlmostComplexField n (lgCover x) (lgCoverTangent x q))))) = _
  rw [map_smul, map_sub, hi, map_smul, map_sub,
    cotangentTangentCoframe_almostComplex, logarithmicAlmostComplexField_cover]
  dsimp only [A]
  rw [D.legendre_derivative_coframe x q,
    D.legendre_derivative_coframe x (coordinateComplexStructure n q)]
  apply Prod.ext <;> simp [coordinateComplexStructure_apply]

/-- The actual real matrix of the normalization on the logarithmic frame. -/
def RetainedLegendrePotential.normalizationMatrix
    (_D : RetainedLegendrePotential φEnd φ) (u : RealSpace n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (2 : ℝ)⁻¹ * ((fderiv ℝ (coordinateGradient φ) u (Pi.single i 1)) j + (Pi.single i 1 : RealSpace n) j)

/-- In the fixed logarithmic canonical square the normalized endpoint
section is a real determinant squared times the literal logarithmic section. -/
theorem RetainedLegendrePotential.normalized_legendre_tensor
    (D : RetainedLegendrePotential φEnd φ) (I : ToricInput n) (x : TangentCoordinates n) :
    (D.legendreMaslov.changeCompatibleStructure (D.nativeMaslov I).J
      (D.nativeMaslov I).compatible).tensor (lgCover x) =
      (((D.normalizationMatrix x.1).det ^ 2 : ℝ) : ℂ) •
        (D.nativeMaslov I).tensor (lgCover x) := by
  let S := D.legendreMaslov.changeCompatibleStructure (D.nativeMaslov I).J
    (D.nativeMaslov I).compatible
  let frame : Fin n ⊕ Fin n → TangentCoordinates n :=
    fun i => verticalFrame n (i.elim id id)
  have he : S.tensor (lgCover x) (fun i => lgCoverTangent x (frame i)) =
      (((D.normalizationMatrix x.1).det ^ 2 : ℝ) : ℂ) := by
    change cotangentSquaredVolumeTensor n (D.legendre (lgCover x))
      (fun i => mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) D.legendre (lgCover x)
        (compatibleComplexTransport (D.legendreMaslov.J (lgCover x))
          (logarithmicAlmostComplexField n (lgCover x)) (lgCoverTangent x (frame i)))) = _
    change coordinateSquaredVolumeValue (fun i =>
      cotangentTangentCoframe (D.legendre (lgCover x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) D.legendre (lgCover x)
          (compatibleComplexTransport (D.legendreMaslov.J (lgCover x))
            (logarithmicAlmostComplexField n (lgCover x)) (lgCoverTangent x (frame i))))) = _
    have hcoords : (fun i : Fin n ⊕ Fin n =>
      cotangentTangentCoframe (D.legendre (lgCover x))
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) D.legendre (lgCover x)
          (compatibleComplexTransport (D.legendreMaslov.J (lgCover x))
            (logarithmicAlmostComplexField n (lgCover x)) (lgCoverTangent x (frame i))))) =
      (fun i => ((2 : ℝ)⁻¹ • (fderiv ℝ (coordinateGradient φ) x.1 (frame i).1 + (frame i).1),
        (2 : ℝ)⁻¹ • ((frame i).2 + fderiv ℝ (coordinateGradient φ) x.1 (frame i).2))) :=
        funext (fun i => D.normalization_derivative_coframe x (frame i))
    apply Eq.trans (congrArg coordinateSquaredVolumeValue hcoords)
    have hf (i : Fin n) : verticalFrame n i = (Pi.single i 1, 0) := by
      apply Prod.ext
      · funext j; simp [verticalFrame, Pi.single_apply, eq_comm]
      · rfl
    simp only [coordinateSquaredVolumeValue, coordinateVolumeValue, frame,
      Sum.elim_inl, Sum.elim_inr, id_eq, hf, map_zero,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero, Complex.ofReal_zero, add_zero]
    change ((D.normalizationMatrix x.1).map Complex.ofRealHom).det *
      ((D.normalizationMatrix x.1).map Complex.ofRealHom).det = _
    have hd : ((D.normalizationMatrix x.1).map Complex.ofRealHom).det =
        (((D.normalizationMatrix x.1).det : ℝ) : ℂ) :=
      (Complex.ofRealHom.map_det (D.normalizationMatrix x.1)).symm
    exact (congrArg (fun c : ℂ => c * c) hd).trans (by simp [pow_two])
  let C : Model (2 * n) ≃L[ℝ] TangentCoordinates n := lgTangentCoframeEquiv (lgCover x)
  have hframe (i : Fin n ⊕ Fin n) :
      C.symm (verticalFrame n (i.elim id id)) = lgCoverTangent x (frame i) := by
    apply C.injective
    rw [C.apply_symm_apply]
    exact (lgTangentCoframe_lgCover x (frame i)).symm
  ext v
  have hrec := squaredCanonicalTensor_reconstruction C
    (logarithmicAlmostComplexField n (lgCover x))
    (lgTangentCoframe_almostComplex (lgCover x))
    ⟨S.tensor (lgCover x), S.canonical (lgCover x)⟩ v
  have hf : (fun i => C.symm (verticalFrame n (i.elim id id))) =
      (fun i => lgCoverTangent x (frame i)) := funext hframe
  have hcoeff := (congrArg (S.tensor (lgCover x)) hf).trans he
  exact hrec.trans (congrArg (fun c : ℂ =>
    c * coordinateSquaredVolumeValue (fun i => C (v i))) hcoeff)

/-- Nonvanishing of the normalized canonical section forces its real
squared determinant ratio to be strictly positive, also in rank zero. -/
theorem RetainedLegendrePotential.normalized_legendre_positive_ratio
    (D : RetainedLegendrePotential φEnd φ) (I : ToricInput n) :
    ∀ y, ∃ a : ℝ, 0 < a ∧
      (D.legendreMaslov.changeCompatibleStructure (D.nativeMaslov I).J
        (D.nativeMaslov I).compatible).tensor y = (a : ℂ) • (D.nativeMaslov I).tensor y := by
  intro y
  obtain ⟨x, rfl⟩ := lgCover_surjective n y
  have he := D.normalized_legendre_tensor I x
  have hn : (D.normalizationMatrix x.1).det ≠ 0 := by
    intro hz
    have hzero :
        (D.legendreMaslov.changeCompatibleStructure (D.nativeMaslov I).J
          (D.nativeMaslov I).compatible).tensor (lgCover x) = 0 := by
      ext v
      have h := congrArg (fun S : SquaredCanonicalTensor n => S v) he
      simpa [hz, smul_eq_mul] using h
    exact (D.legendreMaslov.changeCompatibleStructure (D.nativeMaslov I).J
      (D.nativeMaslov I).compatible).nowhereZero (lgCover x) hzero
  exact ⟨(D.normalizationMatrix x.1).det ^ 2, sq_pos_of_ne_zero hn, he⟩

/-- The actual prescribed logarithmic potential datum is homotopic to
pullback of the vertical cotangent datum by the same selected Legendre map.
No homotopy or endpoint grading certificate is an input. -/
theorem RetainedLegendrePotential.nativeMaslov_homotopic_legendreMaslov
    (D : RetainedLegendrePotential φEnd φ) (I : ToricInput n) :
    MaslovHomotopic (D.nativeMaslov I) D.legendreMaslov := by
  have hratio := (D.nativeMaslov I).homotopic_of_positive_ratio
    (D.legendreMaslov.changeCompatibleStructure (D.nativeMaslov I).J
      (D.nativeMaslov I).compatible) rfl (D.normalized_legendre_positive_ratio I)
  exact hratio.trans
    (D.legendreMaslov.homotopic_changeCompatibleStructure (D.nativeMaslov I).J
      (D.nativeMaslov I).compatible).symm

/-- The prescribed native potential datum under the retained zero marking. -/
def RetainedLegendrePotential.markedNativeMaslov
    (D : RetainedLegendrePotential φEnd φ) (I : ToricInput n) (P : WitnessedPair n)
    (q : P.ambientManifold.SmoothEquiv (lgManifold n))
    (hq : P.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
      P.ambientCompletion.ambient.primitive) : P.Maslov :=
  pullbackPrimitiveMaslovRepresentative P.ambientManifold (lgManifold n)
    P.ambientCompletion.ambient.primitive (lambdaPotentialForm φ) q
    (isSmoothForm_lambdaPotentialForm D.smooth) hq (D.nativeMaslov I)

/-- The retained endpoint identification itself carries the native
logarithmic datum to its prescribed vertical datum. The only map input is
the literal Legendre equation already proved by the endpoint producer. -/
theorem RetainedLegendrePotential.graded_cotangentIdentification
    (D : RetainedLegendrePotential φEnd φ) (I : ToricInput n) (P : WitnessedPair n)
    (q : P.ambientManifold.SmoothEquiv (lgManifold n))
    (hq : P.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
      P.ambientCompletion.ambient.primitive)
    (E : CotangentPairData n) (C : CompletionIdentification P E.pair)
    (hmap : ∀ y, E.marking (C.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) :
    Nonempty (GradedCompletionIdentification C (D.markedNativeMaslov I P q hq) E.verticalMaslov) := by
  have hf : C.ambientEquiv.trans E.marking = q.trans D.legendre := by
    apply Diffeomorph.ext
    intro y
    exact (hmap y).trans (by simp [RetainedLegendrePotential.legendre, D.gradient_eq])
  have hform : P.ambientManifold.pullback (lgManifold n) q
      ((lgManifold n).exteriorDerivative (lambdaPotentialForm φ)) = P.ambientSymplecticForm := by
    have hd := P.ambientManifold.exteriorDerivative_pullback (lgManifold n)
      q.toContMDiffMap (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm D.smooth)
    exact hd.symm.trans (congrArg P.ambientManifold.exteriorDerivative hq)
  obtain ⟨h⟩ := D.nativeMaslov_homotopic_legendreMaslov I
  let H := h.pullback q hform
  have hJ : pullbackAlmostComplex P.ambientManifold (lgManifold n) q D.legendreMaslov.J =
      pullbackAlmostComplex P.ambientManifold E.pair.ambientManifold C.ambientEquiv E.verticalMaslov.J := by
    change pullbackAlmostComplex P.ambientManifold (lgManifold n) q
      (pullbackAlmostComplex (lgManifold n) (cotangentManifold n) D.legendre
        (cotangentAlmostComplexField n)) =
      pullbackAlmostComplex P.ambientManifold E.pair.ambientManifold C.ambientEquiv
        (pullbackAlmostComplex E.pair.ambientManifold (cotangentManifold n) E.marking
          (cotangentAlmostComplexField n))
    calc
      _ = pullbackAlmostComplex P.ambientManifold (cotangentManifold n)
          (q.trans D.legendre) (cotangentAlmostComplexField n) :=
        (pullbackAlmostComplex_trans _ _ _ q D.legendre _).symm
      _ = pullbackAlmostComplex P.ambientManifold (cotangentManifold n)
          (C.ambientEquiv.trans E.marking) (cotangentAlmostComplexField n) :=
        congrArg (fun f => pullbackAlmostComplex P.ambientManifold (cotangentManifold n) f
          (cotangentAlmostComplexField n)) hf.symm
      _ = _ := pullbackAlmostComplex_trans _ _ _ C.ambientEquiv E.marking _
  have hT : pullbackSquaredTensor P.ambientManifold (lgManifold n) q D.legendreMaslov.tensor =
      pullbackSquaredTensor P.ambientManifold E.pair.ambientManifold C.ambientEquiv E.verticalMaslov.tensor := by
    change pullbackSquaredTensor P.ambientManifold (lgManifold n) q
      (pullbackSquaredTensor (lgManifold n) (cotangentManifold n) D.legendre
        (cotangentSquaredVolumeTensor n)) =
      pullbackSquaredTensor P.ambientManifold E.pair.ambientManifold C.ambientEquiv
        (pullbackSquaredTensor E.pair.ambientManifold (cotangentManifold n) E.marking
          (cotangentSquaredVolumeTensor n))
    calc
      _ = pullbackSquaredTensor P.ambientManifold (cotangentManifold n)
          (q.trans D.legendre) (cotangentSquaredVolumeTensor n) :=
        (pullbackSquaredTensor_trans _ _ _ q D.legendre _).symm
      _ = pullbackSquaredTensor P.ambientManifold (cotangentManifold n)
          (C.ambientEquiv.trans E.marking) (cotangentSquaredVolumeTensor n) :=
        congrArg (fun f => pullbackSquaredTensor P.ambientManifold (cotangentManifold n) f
          (cotangentSquaredVolumeTensor n)) hf.symm
      _ = _ := pullbackSquaredTensor_trans _ _ _ C.ambientEquiv E.marking _
  exact ⟨{
    family := H.family
    sourceJ := H.sourceJ
    targetJ := H.targetJ.trans hJ
    sourceSection := H.sourceSection
    targetSection := H.targetSection.trans hT }⟩

/-- The same actual retained endpoint and identification come with their
constructed grading lift and prescribed vertical target datum. -/
theorem CompletedHittingRibbonFamily.exists_retained_graded_cotangentEndpoint
    {I : ToricInput n} {φEnd φ : RealSpace n → ℝ}
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
    (hzero : (L parameterOne).primitive = O.domain.extension.pullback (lgManifold n)
      O.nativeEmbedding.map (lambdaPotentialForm φ))
    (hcore : (O.nativeEmbedding.comp O.domain.boundaryInclusion).map '' H.deformation.target.embeddedCore =
      tailoringLegendreConic I φEnd ∩ range (O.nativeEmbedding.comp O.domain.boundaryInclusion).map) :
    ∃ q : H.deformation.target.ambientManifold.SmoothEquiv (lgManifold n),
      ∃ hq : H.deformation.target.ambientManifold.pullback (lgManifold n) q (lambdaPotentialForm φ) =
        H.deformation.target.ambientCompletion.ambient.primitive,
      (∀ x, q (H.deformation.target.ambientCompletion.inclusion.map
        (H.deformation.target.ambientDomain.domain.boundaryInclusion.map x)) =
          (O.nativeEmbedding.comp O.domain.boundaryInclusion).map x) ∧
      ∃ E : CotangentPairData n, ∃ C : CompletionIdentification H.deformation.target E.pair,
        (∀ y, E.marking (C.ambientEquiv y) = ((q y).2, coordinateGradient φ (q y).1)) ∧
        E.pair.ribbonDomain = H.deformation.target.ribbonDomain ∧
        HEq E.pair.ribbonCompletion H.deformation.target.ribbonCompletion ∧
        HEq C.ribbonEquiv.map (id : H.deformation.target.ribbonDomain.domain.extension.Point →
          H.deformation.target.ribbonDomain.domain.extension.Point) ∧ C.scale = 1 ∧
        (∀ x, E.boundaryCoordinates (C.boundaryEquiv x) =
          tailoringRadialProjection φEnd ((O.nativeEmbedding.comp O.domain.boundaryInclusion).map x)) ∧
        (∀ x, E.pair.witness (C.boundaryEquiv x) =
          Real.sqrt (realSquaredNorm (coordinateGradient φEnd
            ((O.nativeEmbedding.comp O.domain.boundaryInclusion).map x).1)) * H.deformation.target.witness x) ∧
        E.embeddedCore = fltzLink I ∧
        Nonempty (GradedCompletionIdentification C
          (Dφ.markedNativeMaslov I H.deformation.target q hq) E.verticalMaslov) := by
  obtain ⟨q, hq, hb, E, C, hmap, hr, hc, hid, hs, hbound, hw, hcoreE⟩ :=
    H.exists_retained_cotangentEndpoint Dφ hstrong hA hlevelEq hgradient hout
      O hD hboundary hzero hcore
  exact ⟨q, hq, hb, E, C, hmap, hr, hc, hid, hs, hbound, hw, hcoreE,
    Dφ.graded_cotangentIdentification I H.deformation.target q hq E C hmap⟩

end FsFltz
