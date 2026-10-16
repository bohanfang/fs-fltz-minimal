import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovGerms
import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovDescent
import FsFltz.Geometry.CoordinateCoframePullback
import FsFltz.Geometry.CoordinateCoframeScalarPullback

/-!
# Smooth descent of the preselected original completed Maslov data

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. Source-only coframe/scalar germs are transported
through the actual constructed inverse comparisons and identified with the
same chart-independent field and full tensor. Real-open neighborhoods cover
both parameter endpoints and are shrunk to the retained original bases.

The supplied source data and their extension convention are explicit inputs.
This foundational representation does not prove the geometric target or
construct its prescribed endpoint grading or finite chain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry

/-- The actual derivative of the inverse diffeomorphism is the inverse
continuous linear map, so the usual Maslov pullback is inverse conjugation. -/
theorem pullbackAlmostComplex_eq_inverseDerivative {n : ℕ}
    (X Y : SmoothManifold (2 * n)) (f : X.SmoothEquiv Y)
    (J : AlmostComplexField Y) (x : X.Point) :
    pullbackAlmostComplex X Y f J x =
      (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x).inverse.comp
        ((J (f x)).comp (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (2 * n)) f x)) := by
  have h := ContinuousLinearMap.inverse_eq
    (marking_mfderiv_inverse_right X Y f x) (marking_mfderiv_inverse_left X Y f x)
  rw [h]
  rfl

/-- A source coframe intertwining the prescribed complex field still
intertwines its actual inverse pullback. All tangent models may differ. -/
theorem coframe_intertwines_inverseConjugation {n : ℕ} {V F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] TangentCoordinates n) (D : V →L[ℝ] F) (hD : D.IsInvertible)
    (J : F →L[ℝ] F)
    (hB : ∀ v, B (J v) = coordinateComplexStructure n (B v)) (v : V) :
    (B.comp D) ((D.inverse.comp (J.comp D)) v) =
      coordinateComplexStructure n ((B.comp D) v) := by
  change B (D (D.inverse (J (D v)))) = coordinateComplexStructure n (B (D v))
  rw [hD.self_apply_inverse]
  exact hB (D v)

end FsFltz.Geometry

namespace FsFltz.Geometry.IntrinsicSmoothBundle

local instance {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] :
    ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ

local instance {k : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M] :
    IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ))
    (IntrinsicBoundary.Point k M) ℝ

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

variable
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Literal inverse-conjugation formula in the original completed tangent
model, obtained from all-chart pointwise recovery and actual reindexing. -/
theorem descendedJ_nativeInverse_formula
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (y : Q.source.ambientManifold.Point) :
    let F := L.localCompletionFamily c t ht
    let a := F.ambientSourceSliceEquiv L g s Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc)
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) a.symm y
    S.descendedJ g hg hbase Q eAs hp hc s y =
      D.inverse.comp ((S.nativeJ c t ht s hs (a.symm y)).comp D) := by
  rw [S.descendedJ_eq_inverse g hg hbase Q eAs hp hc c t ht s hs,
    pullbackAlmostComplex_eq_inverseDerivative]
  exact CompletedMaslovDimension.comparison_inverse_conjugation hdim
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient
    Q.source.ambientManifold
    ((L.localCompletionFamily c t ht).ambientSourceSliceEquiv L g s Q eAs
      ((L.localCompletionFamily c t ht).ambientEndpointSliceComparison
        L g hg hbase s hs Q hdim eAs hp hc)) (S.J c t ht s hs) y

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Literal inverse pullback of the full tensor in the original completed
tangent model, with every original slot retained. -/
theorem descendedTensor_nativeInverse_formula
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (y : Q.source.ambientManifold.Point) :
    let F := L.localCompletionFamily c t ht
    let a := F.ambientSourceSliceEquiv L g s Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s hs Q hdim eAs hp hc)
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) a.symm y
    S.descendedTensor g hg hbase Q eAs hp hc s y =
      (S.nativeTensor c t ht s hs (a.symm y)).compContinuousLinearMap (fun _ => D) := by
  rw [S.descendedTensor_eq_inverse g hg hbase Q eAs hp hc c t ht s hs]
  exact CompletedMaslovDimension.comparison_inverse_tensor hdim
    ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient
    Q.source.ambientManifold
    ((L.localCompletionFamily c t ht).ambientSourceSliceEquiv L g s Q eAs
      ((L.localCompletionFamily c t ht).ambientEndpointSliceComparison
        L g hg hbase s hs Q hdim eAs hp hc)) (S.tensor c t ht s hs) y

end OriginalLocalCompletionMaslovData

namespace LocalCompletionFamily

variable {c : OriginalCompactChart (k := k) (M := M) (E := E)} {t : Parameter}
  (F : LocalCompletionFamily P c t)

omit [T2Space M] [SecondCountableTopology M] in
/-- The derivative of the actual real interior inverse germ factors through
the original inclusion and a single fixed source chart. -/
theorem ambientReferenceInverse_interiorChart_mfderiv
    (U : Set (ℝ × Q.source.ambientManifold.Point)) (hU : IsOpen U)
    (γ : ℝ × Q.source.ambientManifold.Point → IntrinsicInterior.Point k M)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ γ U)
    (heq : ∀ (s : F.base) y, (s.val.val, y) ∈ U →
      (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
        totalInterior F.native.patches (s.val, γ (s.val.val, y)))
    (s : F.base) (y : Q.source.ambientManifold.Point) (hy : (s.val.val, y) ∈ U)
    (u : IntrinsicInterior.Point k M)
    (hchart : γ (s.val.val, y) ∈ (chartAt (Model (k + 1)) u).source) :
    let a := F.ambientSourceSliceEquiv L g s.val Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => chartAt (Model (k + 1)) u (γ (s.val.val, z))) y =
      (F.interiorMaslovCoordinateDifferential s.val u (γ (s.val.val, y))).comp
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) a.symm y) := by
  let a := F.ambientSourceSliceEquiv L g s.val Q eAs
    (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)
  have hgs : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1))
      (fun z => γ (s.val.val, z)) y :=
    ((hγ.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hUy : ∀ᶠ z in 𝓝 y, (s.val.val, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
  have hs : a.symm =ᶠ[𝓝 y]
      (interiorIn (F.native.patches s.val) ∘ fun z => γ (s.val.val, z)) := by
    filter_upwards [hUy] with z hz
    exact F.ambientSourceSliceEquiv_symm_eq_interior_of_total L g hg hbase Q hdim eAs hp hc
      s z (γ (s.val.val, z)) (heq s z hz)
  exact mfderiv_interiorChart_of_completionInterior_factorization F.native.width_pos
    (F.native.collar s.val) (F.native.embedding s.val) (F.native.smooth s.val)
    (F.native.boundary s.val) (F.native.inverse s.val) (F.native.zero s.val)
    Q.source.ambientManifold a (fun z => γ (s.val.val, z)) y hgs hs u hchart

local instance : ChartedSpace (Model (k + 1)) (Band F.native.width (IntrinsicBoundary.Point k M)) :=
  bandChartedSpace F.native.width

omit [T2Space M] [SecondCountableTopology M] in
/-- The same factorization on the full signed cylinder includes the radial
sign change and the derivative of the original cylinder inclusion. -/
theorem ambientReferenceInverse_endChart_mfderiv
    (U : Set (ℝ × Q.source.ambientManifold.Point)) (hU : IsOpen U)
    (γ : ℝ × Q.source.ambientManifold.Point → IntrinsicBoundary.Point k M × ℝ)
    (hγ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ γ U)
    (heq : ∀ (s : F.base) y, (s.val.val, y) ∈ U →
      ∃ p : Band F.native.width (IntrinsicBoundary.Point k M),
        p.val = (-(γ (s.val.val, y)).2, (γ (s.val.val, y)).1) ∧
        (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
          totalCylinder F.native.patches (s.val, p))
    (s : F.base) (y : Q.source.ambientManifold.Point) (hy : (s.val.val, y) ∈ U)
    (u : IntrinsicBoundary.Point k M × ℝ)
    (hchart : γ (s.val.val, y) ∈ (chartAt (Model k × ℝ) u).source)
    (p : Band F.native.width (IntrinsicBoundary.Point k M))
    (hpcoord : endBandCoordinates p = γ (s.val.val, y))
    (hpeq : (F.ambientReferenceTotalInverse L g hg hbase Q hdim eAs hp hc (s, y)).val =
      totalCylinder F.native.patches (s.val, p)) :
    let a := F.ambientSourceSliceEquiv L g s.val Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)
    mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => chartAt (Model k × ℝ) u (γ (s.val.val, z))) y =
      (F.endMaslovCoordinateDifferential s.val u p).comp
        (mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) a.symm y) := by
  let a := F.ambientSourceSliceEquiv L g s.val Q eAs
    (F.ambientEndpointSliceComparison L g hg hbase s.val s.property Q hdim eAs hp hc)
  have hγm : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model k × ℝ) ∞ γ U := by rwa [modelWithCornersSelf_prod]
  have hgs : MDifferentiableAt 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model k × ℝ)
      (fun z => γ (s.val.val, z)) y :=
    ((hγm.contMDiffAt (hU.mem_nhds hy)).comp y
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have hUy : ∀ᶠ z in 𝓝 y, (s.val.val, z) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hy)
  have hs : ∀ᶠ z in 𝓝 y, ∃ p' : Band F.native.width (IntrinsicBoundary.Point k M),
      endBandCoordinates p' = γ (s.val.val, z) ∧ a.symm z = cylinder (F.native.patches s.val) p' := by
    filter_upwards [hUy] with z hz
    obtain ⟨p', hp'coord, hp'eq⟩ := heq s z hz
    refine ⟨p', ?_, F.ambientSourceSliceEquiv_symm_eq_cylinder_of_total
      L g hg hbase Q hdim eAs hp hc s z p' hp'eq⟩
    dsimp only [endBandCoordinates]
    rw [hp'coord]
    simp only [neg_neg]
  have h := mfderiv_endChart_of_completionCylinder_factorization F.native.width_pos
    (F.native.collar s.val) (F.native.embedding s.val) (F.native.smooth s.val)
    (F.native.boundary s.val) (F.native.inverse s.val) (F.native.zero s.val)
    Q.source.ambientManifold a (fun z => γ (s.val.val, z)) y hgs p
    (F.ambientSourceSliceEquiv_symm_eq_cylinder_of_total L g hg hbase Q hdim eAs hp hc
      s y p hpeq) hpcoord hs u hchart
  dsimp only [endMaslovCoordinateDifferential]
  rw [hpcoord]
  exact h

end LocalCompletionFamily

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)
  (hS : OriginalLocalCompletionMaslovCoframeGerms S)
  (eBs : ∀ u, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
    (Q.pair u).ambientDomain.domain.boundary)
  (hb : ∀ u b, (Q.pair u).ambientDomain.domain.boundaryInclusion.map (eBs u b) =
    (eAs u b.val).val)
  (hsquareB : ∀ u b, (Q.ambientPresentation u).boundaryEquiv (eBs parameterZero b) = eBs u b)
  (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
  (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
  (hsquareA : ∀ s x, (Q.ambientPresentation s).extensionEquiv
    (eAs parameterZero (R s.val x)).val = (eAs s x).val)

include hS eBs hb hsquareB R hR hsquareA in
/-- Source-local smooth coframes and scalar germs transport through the
constructed inverse comparison from any original retained chart. Both
extension fields are literally the existing descended fields wherever the
parameter is in the interval. Relative base openness is used to produce
this unrestricted interval matching on a smaller real-open neighborhood. -/
theorem exists_local_descendedMaslovExtension_from_chart
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base)
    (y : Q.source.ambientManifold.Point) :
    ∃ U : Set (ℝ × Q.source.ambientManifold.Point), IsOpen U ∧ (s.val, y) ∈ U ∧
      ∃ B : (ℝ × Q.source.ambientManifold.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n,
        IsSmoothVerticalCoframeOn Q.source.ambientManifold B U ∧
        (∀ z ∈ U, (B z).IsInvertible) ∧
        ∃ a : (ℝ × Q.source.ambientManifold.Point) → ℂ,
          ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞ a U ∧
          IsSmoothVerticalEndomorphismOn Q.source.ambientManifold
            (fun z => coframeComplexStructure (B z)) U ∧
          IsSmoothVerticalSquaredTensorOn Q.source.ambientManifold
            (fun z => a z • coframeSquaredGenerator (B z)) U ∧
          ∀ (v : Parameter) z, (v.val, z) ∈ U →
            coframeComplexStructure (B (v.val, z)) = S.descendedJ g hg hbase Q eAs hp hc v z ∧
            a (v.val, z) • coframeSquaredGenerator (B (v.val, z)) =
              S.descendedTensor g hg hbase Q eAs hp hc v z := by
  let F := L.localCompletionFamily c t ht
  obtain ⟨A, hA, htrace⟩ := isOpen_induced_iff.mp F.base_open
  have hsA : s.val ∈ A := by
    change s ∈ Subtype.val ⁻¹' A
    rw [htrace]
    exact hs
  rcases F.ambientReferenceInverse_has_invertible_patchGerms L g hg hbase Q hdim eAs hp hc
      eBs hb hsquareB R hR hsquareA ⟨s, hs⟩ y with
    ⟨U₀, hU₀, hpU₀, γ, hγ, u, hchart, hi, heq⟩ |
    ⟨U₀, hU₀, hpU₀, γ, hγ, u, hchart, hrad, hi, heq⟩
  · obtain ⟨V, hV, hpV, C, hC, hCi, a, ha, hsource⟩ :=
      hS.interior c t ht s hs u (γ (s.val, y)) (hchart _ hpU₀)
    let φ := fun z : ℝ × Q.source.ambientManifold.Point =>
      chartAt (Model (k + 1)) u (γ z)
    have hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model (k + 1)) ∞ φ U₀ :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := u)).comp hγ hchart
    obtain ⟨W, hW, hpW, hsub, hB, hBi, hJ, ha', hT⟩ :=
      exists_coordinateCoframeScalar_pullback Q.source.ambientManifold φ hU₀ hφ hi
        (s.val, y) hpU₀ hV hpV C hC hCi a ha
    let U := W ∩ (Prod.fst : ℝ × Q.source.ambientManifold.Point → ℝ) ⁻¹' A
    have hU : IsOpen U := hW.inter (hA.preimage continuous_fst)
    let B := pullbackCoordinateVerticalCoframe Q.source.ambientManifold φ C
    refine ⟨U, hU, ⟨hpW, hsA⟩, B,
      (fun b => (hB b).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
      (fun z hz => hBi z hz.1), (fun z => a (z.1, φ z)), ha'.mono inter_subset_left,
      (fun b => (hJ b).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
      (fun b => (hT b).mono (fun z hz => ⟨hz.1, hz.2.1⟩)), ?_⟩
    intro v z hz
    have hv : v ∈ F.base := by
      rw [← htrace]
      exact hz.2
    have hpoint := F.ambientSourceSliceEquiv_symm_eq_interior_of_total
      L g hg hbase Q hdim eAs hp hc ⟨v, hv⟩ z (γ (v.val, z))
      (heq ⟨v, hv⟩ z (hsub hz.1).1)
    let e := F.ambientSourceSliceEquiv L g v Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase v hv Q hdim eAs hp hc)
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) e.symm z
    have hD : D.IsInvertible := e.symm.isInvertible_mfderiv (by simp)
    have hd := F.ambientReferenceInverse_interiorChart_mfderiv g hg hbase Q eAs hp hc
      U₀ hU₀ γ hγ heq ⟨v, hv⟩ z (hsub hz.1).1 u (hchart _ (hsub hz.1).1)
    obtain ⟨hCJ, hTS⟩ := hsource v hv (γ (v.val, z))
      (hchart _ (hsub hz.1).1) (hsub hz.1).2
    have hBJ : ∀ ξ, B (v.val, z) (S.descendedJ g hg hbase Q eAs hp hc v z ξ) =
        coordinateComplexStructure n (B (v.val, z) ξ) := by
      intro ξ
      dsimp only [B, pullbackCoordinateVerticalCoframe, φ]
      rw [hd, S.descendedJ_nativeInverse_formula g hg hbase Q eAs hp hc c t ht v hv z,
        hpoint]
      exact coframe_intertwines_inverseConjugation (V := Model (2 * n)) (F := Model (k + 1))
        ((C (v.val, φ (v.val, z))).comp
          (F.interiorMaslovCoordinateDifferential v u (γ (v.val, z)))) D hD
        (S.nativeJ c t ht v hv (interiorIn (F.native.patches v) (γ (v.val, z)))) hCJ ξ
    refine ⟨coframeComplexStructure_eq _ (hBi _ hz.1) _ hBJ, ?_⟩
    dsimp only [B, pullbackCoordinateVerticalCoframe, φ]
    rw [hd, S.descendedTensor_nativeInverse_formula g hg hbase Q eAs hp hc c t ht v hv z,
      hpoint, hTS]
    ext ξ
    rfl
  · obtain ⟨p, hpcoord₀, hpeq₀⟩ := heq ⟨s, hs⟩ y hpU₀
    have hpcoord : endBandCoordinates p = γ (s.val, y) := by
      dsimp only [endBandCoordinates]
      rw [hpcoord₀]
      simp only [neg_neg]
    obtain ⟨V, hV, hpV, C, hC, hCi, a, ha, hsource⟩ :=
      hS.cylinder c t ht s hs u p (by rw [hpcoord]; exact hchart _ hpU₀)
    rw [hpcoord] at hpV
    let φ := fun z : ℝ × Q.source.ambientManifold.Point =>
      chartAt (Model k × ℝ) u (γ z)
    have hγm : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model k × ℝ) ∞ γ U₀ := by rwa [modelWithCornersSelf_prod]
    have hφ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n)))
        𝓘(ℝ, Model k × ℝ) ∞ φ U₀ :=
      (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := u)).comp hγm hchart
    obtain ⟨W, hW, hpW, hsub, hB, hBi, hJ, ha', hT⟩ :=
      exists_coordinateCoframeScalar_pullback Q.source.ambientManifold φ hU₀ hφ hi
        (s.val, y) hpU₀ hV hpV C hC hCi a ha
    let U := W ∩ (Prod.fst : ℝ × Q.source.ambientManifold.Point → ℝ) ⁻¹' A
    have hU : IsOpen U := hW.inter (hA.preimage continuous_fst)
    let B := pullbackCoordinateVerticalCoframe Q.source.ambientManifold φ C
    refine ⟨U, hU, ⟨hpW, hsA⟩, B,
      (fun b => (hB b).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
      (fun z hz => hBi z hz.1), (fun z => a (z.1, φ z)), ha'.mono inter_subset_left,
      (fun b => (hJ b).mono (fun z hz => ⟨hz.1, hz.2.1⟩)),
      (fun b => (hT b).mono (fun z hz => ⟨hz.1, hz.2.1⟩)), ?_⟩
    intro v z hz
    have hv : v ∈ F.base := by
      rw [← htrace]
      exact hz.2
    obtain ⟨q, hqcoord₀, hqeq⟩ := heq ⟨v, hv⟩ z (hsub hz.1).1
    have hqcoord : endBandCoordinates q = γ (v.val, z) := by
      dsimp only [endBandCoordinates]
      rw [hqcoord₀]
      simp only [neg_neg]
    have hpoint := F.ambientSourceSliceEquiv_symm_eq_cylinder_of_total
      L g hg hbase Q hdim eAs hp hc ⟨v, hv⟩ z q hqeq
    let e := F.ambientSourceSliceEquiv L g v Q eAs
      (F.ambientEndpointSliceComparison L g hg hbase v hv Q hdim eAs hp hc)
    let D := mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, Model (k + 1)) e.symm z
    have hD : D.IsInvertible := e.symm.isInvertible_mfderiv (by simp)
    have hd := F.ambientReferenceInverse_endChart_mfderiv g hg hbase Q eAs hp hc
      U₀ hU₀ γ hγ heq ⟨v, hv⟩ z (hsub hz.1).1 u (hchart _ (hsub hz.1).1)
      q hqcoord hqeq
    obtain ⟨hCJ, hTS⟩ := hsource v hv q
      (by rw [hqcoord]; exact hchart _ (hsub hz.1).1)
      (by rw [hqcoord]; exact (hsub hz.1).2)
    rw [hqcoord] at hCJ hTS
    have hBJ : ∀ ξ, B (v.val, z) (S.descendedJ g hg hbase Q eAs hp hc v z ξ) =
        coordinateComplexStructure n (B (v.val, z) ξ) := by
      intro ξ
      dsimp only [B, pullbackCoordinateVerticalCoframe, φ]
      rw [hd, S.descendedJ_nativeInverse_formula g hg hbase Q eAs hp hc c t ht v hv z,
        hpoint]
      exact coframe_intertwines_inverseConjugation (V := Model (2 * n)) (F := Model (k + 1))
        ((C (v.val, φ (v.val, z))).comp (F.endMaslovCoordinateDifferential v u q)) D hD
        (S.nativeJ c t ht v hv (cylinder (F.native.patches v) q)) hCJ ξ
    refine ⟨coframeComplexStructure_eq _ (hBi _ hz.1) _ hBJ, ?_⟩
    dsimp only [B, pullbackCoordinateVerticalCoframe, φ]
    rw [hd, S.descendedTensor_nativeInverse_formula g hg hbase Q eAs hp hc c t ht v hv z,
      hpoint, hTS]
    ext ξ
    rfl

include hS eBs hb hsquareB R hR hsquareA in
/-- The original charts cover every actual parameter, including zero and
one. Source-native coframe/scalar germs therefore give smooth local real
extensions of the same descended complex field and full tensor everywhere. -/
theorem exists_local_descendedMaslovExtension
    (s : Parameter) (y : Q.source.ambientManifold.Point) :
    ∃ U : Set (ℝ × Q.source.ambientManifold.Point), IsOpen U ∧ (s.val, y) ∈ U ∧
      ∃ B : (ℝ × Q.source.ambientManifold.Point) → Model (2 * n) →L[ℝ] TangentCoordinates n,
        IsSmoothVerticalCoframeOn Q.source.ambientManifold B U ∧
        (∀ z ∈ U, (B z).IsInvertible) ∧
        ∃ a : (ℝ × Q.source.ambientManifold.Point) → ℂ,
          ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, ℂ) ∞ a U ∧
          IsSmoothVerticalEndomorphismOn Q.source.ambientManifold
            (fun z => coframeComplexStructure (B z)) U ∧
          IsSmoothVerticalSquaredTensorOn Q.source.ambientManifold
            (fun z => a z • coframeSquaredGenerator (B z)) U ∧
          ∀ (v : Parameter) z, (v.val, z) ∈ U →
            coframeComplexStructure (B (v.val, z)) = S.descendedJ g hg hbase Q eAs hp hc v z ∧
            a (v.val, z) • coframeSquaredGenerator (B (v.val, z)) =
              S.descendedTensor g hg hbase Q eAs hp hc v z := by
  let c := originalMaslovChartAt (k := k) (M := M) (E := E) s
  let ht := originalMaslovChartAt_mem (k := k) (M := M) (E := E) s
  exact S.exists_local_descendedMaslovExtension_from_chart g hg hbase Q eAs hp hc hS
    eBs hb hsquareB R hR hsquareA c s ht s (L.localCompletionFamily c s ht).base_mem y

end OriginalLocalCompletionMaslovData

end FsFltz.Geometry.IntrinsicSmoothBundle

namespace FsFltz.Geometry

end FsFltz.Geometry
