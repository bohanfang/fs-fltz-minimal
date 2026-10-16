import FsFltz.Geometry.OriginalBundleFiniteRealization

/-!
# Original junctions on the realizations retained throughout a finite path

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 171–199;
`def:maslov`, lines 225–234; and `sec:lean`, lines 788–814.
Vertices name an original bundle and a parameter. Junction inputs contain
only original local completions, strict maps, whole-ribbon maps and original
Maslov homotopies. Their identifications and grading lifts are constructed on
the same realization used by every other arrow incident to either bundle.
The original ambient and ribbon manifolds can differ at every vertex.

This is conditional transport of supplied original geometric data. It does
not establish the existence of the toric path or the FLTZ endpoint grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- A literal original positive-ribbon bundle endpoint. -/
structure OriginalPositiveEndpoint (a k n : ℕ) [NeZero n] [NeZero (2 * n - 2)] where
  bundle : OriginalPositiveBundle a k n
  parameter : Parameter

namespace OriginalPositiveEndpoint
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]

/-- The endpoint in the single retained realization of this original bundle. -/
def pair (E : OriginalPositiveEndpoint a k n) : WitnessedPair n :=
  E.bundle.realize.Q.pair E.parameter

/-- The actual slice representative of that same original Maslov family. -/
def maslov (E : OriginalPositiveEndpoint a k n) : E.pair.Maslov :=
  E.bundle.realize.Q.maslovFamilyRepresentative E.bundle.realize.f E.parameter

end OriginalPositiveEndpoint

/-- Original local maps and homotopy between two original endpoints. No
represented pair, identification, represented endpoint equation or grading lift occurs. -/
structure OriginalPositiveJunction {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
    (L R : OriginalPositiveEndpoint a k n) where
  cA : OriginalCompactChart (k := a) (M := L.bundle.A) (E := L.bundle.EA)
  cA' : OriginalCompactChart (k := a) (M := R.bundle.A) (E := R.bundle.EA)
  t : Parameter
  t' : Parameter
  ht : t ∈ cA.val.baseSet
  ht' : t' ∈ cA'.val.baseSet
  hs : L.parameter ∈ (L.bundle.LA.localCompletionFamily cA t ht).base
  hs' : R.parameter ∈ (R.bundle.LA.localCompletionFamily cA' t' ht').base
  ambient : OriginalBundleAmbientJunction L.bundle.LA R.bundle.LA
    (L.bundle.LA.localCompletionFamily cA t ht)
    (R.bundle.LA.localCompletionFamily cA' t' ht') L.parameter R.parameter
    L.bundle.hdimA R.bundle.hdimA
  cM : OriginalCompactChart (k := k) (M := L.bundle.M) (E := L.bundle.EM)
  cM' : OriginalCompactChart (k := k) (M := R.bundle.M) (E := R.bundle.EM)
  tM : Parameter
  tM' : Parameter
  htM : tM ∈ cM.val.baseSet
  htM' : tM' ∈ cM'.val.baseSet
  hsM : L.parameter ∈ (L.bundle.LM.localCompletionFamily cM tM htM).base
  hsM' : R.parameter ∈ (R.bundle.LM.localCompletionFamily cM' tM' htM').base
  ribbon : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) L.bundle.M R.bundle.M ∞
  ribbonGerm : IsLocallyExtendibleNativeMap (k := k) ribbon
  scale : ℝ
  positiveScale : 0 < scale
  primitiveScale : ∀ x,
    (R.bundle.PM.form cM' R.parameter (ribbon x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) ribbon x) =
        scale • L.bundle.PM.form cM L.parameter x
  ribbonSquare : ∀ x, ambient.ψ (L.bundle.PJ.map cM cA L.parameter x) =
    R.bundle.PJ.map cM' cA' R.parameter (ribbon x)
  nativeSource : MaslovRepresentative
    (localMaslovAmbient L.bundle.hdimA L.bundle.LA cA t ht L.parameter).manifold
    ((localMaslovAmbient L.bundle.hdimA L.bundle.LA cA t ht L.parameter).manifold.exteriorDerivative
      (localMaslovAmbient L.bundle.hdimA L.bundle.LA cA t ht L.parameter).primitive)
  nativeTarget : MaslovRepresentative
    (localMaslovAmbient R.bundle.hdimA R.bundle.LA cA' t' ht' R.parameter).manifold
    ((localMaslovAmbient R.bundle.hdimA R.bundle.LA cA' t' ht' R.parameter).manifold.exteriorDerivative
      (localMaslovAmbient R.bundle.hdimA R.bundle.LA cA' t' ht' R.parameter).primitive)
  sourceJ : nativeSource.J = L.bundle.S.J cA t ht L.parameter hs
  sourceTensor : nativeSource.tensor = L.bundle.S.tensor cA t ht L.parameter hs
  targetJ : nativeTarget.J = R.bundle.S.J cA' t' ht' R.parameter hs'
  targetTensor : nativeTarget.tensor = R.bundle.S.tensor cA' t' ht' R.parameter hs'
  homotopy : MaslovHomotopy nativeSource
    (nativeTarget.pullbackTo ambient.Ψ ambient.strictSymplectic.symm)

namespace OriginalPositiveJunction
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {L R : OriginalPositiveEndpoint a k n} (J : OriginalPositiveJunction L R)

/-- The prescribed original whole-ribbon square, with each original model
retained literally. -/
@[reducible] def originalRibbon : OriginalBundlePositiveRibbonJunction J.ambient where
  k := k
  dimension := L.bundle.hdimM
  M := L.bundle.M
  N := R.bundle.M
  μ := L.bundle.PM.form J.cM L.parameter
  ν := R.bundle.PM.form J.cM' R.parameter
  h := J.ribbon
  mapGerm := J.ribbonGerm
  scale := J.scale
  positiveScale := J.positiveScale
  primitiveScale := J.primitiveScale
  j := L.bundle.PJ.map J.cM J.cA L.parameter
  j' := R.bundle.PJ.map J.cM' J.cA' R.parameter
  ribbonSquare := J.ribbonSquare

/-- Original ribbon covariance constructs the junction on the two retained
realizations. All compact primitive and whole-embedding equations are derived. -/
def native : NativeCompletionJunction L.pair R.pair := by
  let F := L.bundle.realize
  let G := R.bundle.realize
  exact J.ambient.toNativeCompletionJunction_of_originalRibbonBundleData
    F.cA G.cA F.heA G.heA F.hbaseA G.hbaseA J.hs J.hs'
    F.Q G.Q F.eAs G.eAs F.hp G.hp F.hc G.hc J.originalRibbon
    (F.eBs L.parameter) (G.eBs R.parameter)
    (F.geometry L.parameter).1 (G.geometry R.parameter).1
    L.bundle.PM R.bundle.PM L.bundle.LM R.bundle.LM L.bundle.PJ R.bundle.PJ
    J.cM J.cM' (L.bundle.LM.localCompletionFamily J.cM J.tM J.htM)
    (R.bundle.LM.localCompletionFamily J.cM' J.tM' J.htM') J.hsM J.hsM'
    rfl rfl rfl rfl F.cM G.cM F.heM G.heM F.hbaseM G.hbaseM
    F.eMs G.eMs F.hpM G.hpM F.hcM G.hcM
    (F.geometry L.parameter).2.2.2.1 (G.geometry R.parameter).2.2.2.1

/-- Full original endpoint field and tensor recovery construct the grade on
that exact whole-ribbon junction, without a supplied represented lift. -/
def graded : GradedCompletionIdentification J.native.identification L.maslov R.maslov := by
  let F := L.bundle.realize
  let G := R.bundle.realize
  have hF := L.bundle.S.pullback_maslovFamilyRepresentative_descended
    F.cA F.heA F.hbaseA F.Q F.eAs F.hp F.hc F.f F.familyJ F.familyTensor
    J.cA J.t J.ht L.parameter J.hs
  have hG := R.bundle.S.pullback_maslovFamilyRepresentative_descended
    G.cA G.heA G.hbaseA G.Q G.eAs G.hp G.hc G.f G.familyJ G.familyTensor
    J.cA' J.t' J.ht' R.parameter J.hs'
  have hnativeJF : J.nativeSource.J =
      pullbackAlmostComplex J.native.ambient.X L.pair.ambientManifold
        J.native.ambient.S L.maslov.J := J.sourceJ.trans hF.1.symm
  have hnativeTF : J.nativeSource.tensor =
      pullbackSquaredTensor J.native.ambient.X L.pair.ambientManifold
        J.native.ambient.S L.maslov.tensor := J.sourceTensor.trans hF.2.symm
  have hnativeJG : J.nativeTarget.J =
      pullbackAlmostComplex J.native.ambient.Y R.pair.ambientManifold
        J.native.ambient.S' R.maslov.J := J.targetJ.trans hG.1.symm
  have hnativeTG : J.nativeTarget.tensor =
      pullbackSquaredTensor J.native.ambient.Y R.pair.ambientManifold
        J.native.ambient.S' R.maslov.tensor := J.targetTensor.trans hG.2.symm
  refine J.native.gradedLiftOfOriginalHomotopy J.nativeSource J.nativeTarget J.homotopy
    L.maslov R.maslov ?_ ?_ ?_ ?_
  · intro x v
    rw [hnativeJF]
    exact pullbackAlmostComplex_intertwines _ _ _ _ x v
  · intro x vs
    rw [hnativeTF]
    rfl
  · intro x v
    rw [hnativeJG]
    exact pullbackAlmostComplex_intertwines _ _ _ _ x v
  · intro x vs
    rw [hnativeTG]
    rfl

/-- The entire original strict map is conjugated by these same endpoint
comparisons. -/
theorem identification_ambientEquiv : J.native.identification.ambientEquiv =
    (J.native.ambient.S.symm.trans J.ambient.Ψ).trans J.native.ambient.S' :=
  J.native.identification_ambientEquiv

/-- The prescribed boundary map is retained on the whole boundary. -/
theorem identification_boundaryEquiv : J.native.identification.boundaryEquiv =
    (J.native.ambient.bS.symm.trans J.ambient.ψ).trans J.native.ambient.bS' :=
  J.native.identification_boundaryEquiv

/-- The original real shift is retained; it need not be constant or positive. -/
theorem identification_shift : J.native.identification.shift =
    J.ambient.shift ∘ J.native.ambient.bS.symm := J.native.identification_shift

/-- Every real homotopy parameter recovers the prescribed original complex
field under the inverse endpoint comparison. -/
theorem graded_family_J (τ : ℝ) : J.graded.family.J τ =
    pullbackAlmostComplex L.pair.ambientManifold J.native.ambient.X
      J.native.ambient.S.symm (J.homotopy.family.J τ) := rfl

/-- Every real homotopy parameter retains the full original canonical-square
tensor, with both alternating blocks and all slots. -/
theorem graded_family_tensor (τ : ℝ) : J.graded.family.tensor τ =
    pullbackSquaredTensor L.pair.ambientManifold J.native.ambient.X
      J.native.ambient.S.symm (J.homotopy.family.tensor τ) := rfl

end OriginalPositiveJunction

/-- A literal original zero-ribbon bundle endpoint, including empty ribbons. -/
structure OriginalZeroEndpoint where
  bundle : OriginalZeroBundle
  parameter : Parameter

namespace OriginalZeroEndpoint

/-- The endpoint in the single retained realization of this original bundle. -/
def pair (E : OriginalZeroEndpoint) : WitnessedPair 1 :=
  E.bundle.realize.Q.pair E.parameter

/-- The slice representative of that same original Maslov family. -/
def maslov (E : OriginalZeroEndpoint) : E.pair.Maslov :=
  E.bundle.realize.Q.maslovFamilyRepresentative E.bundle.realize.f E.parameter

end OriginalZeroEndpoint

/-- Original local maps and homotopy between zero-ribbon endpoints. The full
finite ribbons and their map directions are present even if both are empty. -/
structure OriginalZeroJunction (L R : OriginalZeroEndpoint) where
  cA : OriginalCompactChart (k := 1) (M := L.bundle.A) (E := L.bundle.EA)
  cA' : OriginalCompactChart (k := 1) (M := R.bundle.A) (E := R.bundle.EA)
  t : Parameter
  t' : Parameter
  ht : t ∈ cA.val.baseSet
  ht' : t' ∈ cA'.val.baseSet
  hs : L.parameter ∈ (L.bundle.LA.localCompletionFamily cA t ht).base
  hs' : R.parameter ∈ (R.bundle.LA.localCompletionFamily cA' t' ht').base
  ambient : OriginalBundleAmbientJunction L.bundle.LA R.bundle.LA
    (L.bundle.LA.localCompletionFamily cA t ht)
    (R.bundle.LA.localCompletionFamily cA' t' ht') L.parameter R.parameter
    (n := 1) rfl rfl
  cM : OriginalZeroCompactChart (M := L.bundle.M) (E := L.bundle.EM)
  cM' : OriginalZeroCompactChart (M := R.bundle.M) (E := R.bundle.EM)
  hsM : L.parameter ∈ cM.val.baseSet
  hsM' : R.parameter ∈ cM'.val.baseSet
  ribbon : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) L.bundle.M R.bundle.M ∞
  scale : ℝ
  positiveScale : 0 < scale
  ribbonSquare : ∀ x, ambient.ψ (L.bundle.PJ.map cM cA L.parameter x) =
    R.bundle.PJ.map cM' cA' R.parameter (ribbon x)
  nativeSource : MaslovRepresentative
    (localMaslovAmbient (n := 1) rfl L.bundle.LA cA t ht L.parameter).manifold
    ((localMaslovAmbient (n := 1) rfl L.bundle.LA cA t ht L.parameter).manifold.exteriorDerivative
      (localMaslovAmbient (n := 1) rfl L.bundle.LA cA t ht L.parameter).primitive)
  nativeTarget : MaslovRepresentative
    (localMaslovAmbient (n := 1) rfl R.bundle.LA cA' t' ht' R.parameter).manifold
    ((localMaslovAmbient (n := 1) rfl R.bundle.LA cA' t' ht' R.parameter).manifold.exteriorDerivative
      (localMaslovAmbient (n := 1) rfl R.bundle.LA cA' t' ht' R.parameter).primitive)
  sourceJ : nativeSource.J = L.bundle.S.J cA t ht L.parameter hs
  sourceTensor : nativeSource.tensor = L.bundle.S.tensor cA t ht L.parameter hs
  targetJ : nativeTarget.J = R.bundle.S.J cA' t' ht' R.parameter hs'
  targetTensor : nativeTarget.tensor = R.bundle.S.tensor cA' t' ht' R.parameter hs'
  homotopy : MaslovHomotopy nativeSource
    (nativeTarget.pullbackTo ambient.Ψ ambient.strictSymplectic.symm)

namespace OriginalZeroJunction
variable {L R : OriginalZeroEndpoint} (J : OriginalZeroJunction L R)

/-- The prescribed original whole-ribbon square with its entire finite sets. -/
@[reducible] def originalRibbon : OriginalBundleZeroRibbonJunction J.ambient where
  M := L.bundle.M
  N := R.bundle.M
  h := J.ribbon
  scale := J.scale
  positiveScale := J.positiveScale
  j := L.bundle.PJ.map J.cM J.cA L.parameter
  j' := R.bundle.PJ.map J.cM' J.cA' R.parameter
  ribbonSquare := J.ribbonSquare

/-- Original chart covariance constructs the whole zero-ribbon junction on
the same two realizations used by the rest of the itinerary. -/
def native : NativeCompletionJunction L.pair R.pair := by
  let F := L.bundle.realize
  let G := R.bundle.realize
  exact J.ambient.toNativeZeroCompletionJunction_of_originalRibbonBundleData
    F.eA G.eA F.heA G.heA F.hbaseA G.hbaseA J.hs J.hs'
    F.Q G.Q F.eAs G.eAs F.hp G.hp F.hc G.hc J.originalRibbon
    (F.eBs L.parameter) (G.eBs R.parameter)
    (F.geometry L.parameter).1 (G.geometry R.parameter).1
    L.bundle.PJ R.bundle.PJ J.cM J.cM' J.hsM J.hsM' rfl rfl
    F.eM G.eM F.hbaseM G.hbaseM F.eFs G.eFs
    (F.geometry L.parameter).2.1 (G.geometry R.parameter).2.1

/-- Original endpoint recovery derives the four represented field/tensor
laws and grades that exact zero-ribbon identification. -/
def graded : GradedCompletionIdentification J.native.identification L.maslov R.maslov := by
  let F := L.bundle.realize
  let G := R.bundle.realize
  exact J.ambient.gradedZeroLiftOfLocalMaslovHomotopy_of_originalRibbonBundleData
    F.eA G.eA F.heA G.heA F.hbaseA G.hbaseA J.hs J.hs'
    F.Q G.Q F.eAs G.eAs F.hp G.hp F.hc G.hc J.originalRibbon
    L.bundle.PJ R.bundle.PJ J.cM J.cM' J.hsM J.hsM' rfl rfl
    F.eM G.eM F.hbaseM G.hbaseM F.eFs G.eFs
    (F.eBs L.parameter) (G.eBs R.parameter)
    (F.geometry L.parameter).1 (G.geometry R.parameter).1
    (F.geometry L.parameter).2.1 (G.geometry R.parameter).2.1
    L.bundle.S R.bundle.S F.f G.f F.familyJ F.familyTensor G.familyJ G.familyTensor
    J.nativeSource J.nativeTarget J.sourceJ J.sourceTensor J.targetJ J.targetTensor J.homotopy

/-- The same original strict map is retained on the full completion. -/
theorem identification_ambientEquiv : J.native.identification.ambientEquiv =
    (J.native.ambient.S.symm.trans J.ambient.Ψ).trans J.native.ambient.S' :=
  J.native.identification_ambientEquiv

/-- The prescribed map is retained on the whole boundary. -/
theorem identification_boundaryEquiv : J.native.identification.boundaryEquiv =
    (J.native.ambient.bS.symm.trans J.ambient.ψ).trans J.native.ambient.bS' :=
  J.native.identification_boundaryEquiv

/-- The prescribed arbitrary real shift is retained. -/
theorem identification_shift : J.native.identification.shift =
    J.ambient.shift ∘ J.native.ambient.bS.symm := J.native.identification_shift

/-- The original complex field is retained at every real homotopy parameter. -/
theorem graded_family_J (τ : ℝ) : J.graded.family.J τ =
    pullbackAlmostComplex L.pair.ambientManifold J.native.ambient.X
      J.native.ambient.S.symm (J.homotopy.family.J τ) := rfl

/-- The full original canonical-square tensor is retained at every real
homotopy parameter. -/
theorem graded_family_tensor (τ : ℝ) : J.graded.family.tensor τ =
    pullbackSquaredTensor L.pair.ambientManifold J.native.ambient.X
      J.native.ambient.S.symm (J.homotopy.family.tensor τ) := rfl

end OriginalZeroJunction
end FsFltz.Geometry.IntrinsicSmoothBundle
