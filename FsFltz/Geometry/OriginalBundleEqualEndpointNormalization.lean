import FsFltz.Geometry.OriginalBundleFiniteChain

/-!
# Normalizing equal original compact endpoint tuples

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 212–244; `thm:target`, lines 352–415; and
`sec:lean`, lines 766–836. Equality here concerns the original compact
manifolds, their full primitives, the whole ribbon embedding and its witness.
Independent bundle descriptions and their independently retained completions
are allowed. The completion map is constructed from that equality.

These are conditional foundational identifications. They do not construct
the toric chain, full-fiber markings, the FLTZ core or endpoint grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- A compact native manifold, including its original across-boundary
identity germs. These germs will be derived from a bundle self-transition. -/
structure OriginalNativeCompactModel (k : ℕ) where
  Point : Type
  [topology : TopologicalSpace Point]
  [separated : T2Space Point]
  [countable : SecondCountableTopology Point]
  [compact : CompactSpace Point]
  [charted : ChartedSpace (EuclideanHalfSpace (k + 1)) Point]
  [manifold : IsManifold (𝓡∂ (k + 1)) ∞ Point]
  identityGerm : IsLocallyExtendibleNativeMap (k := k) (id : Point → Point)

attribute [instance] OriginalNativeCompactModel.topology OriginalNativeCompactModel.separated
  OriginalNativeCompactModel.countable OriginalNativeCompactModel.compact
  OriginalNativeCompactModel.charted OriginalNativeCompactModel.manifold

namespace OriginalNativeCompactModel
variable {k : ℕ}

/-- Literal equality of compact manifolds has a specified transport map. -/
def equivOfEq {A B : OriginalNativeCompactModel k} (h : A = B) :
    Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) A.Point B.Point ∞ := by
  subst B
  exact Diffeomorph.refl _ _ _

/-- Equality transport extends across the original spatial boundary. -/
theorem equivOfEq_germ {A B : OriginalNativeCompactModel k} (h : A = B) :
    IsLocallyExtendibleNativeMap (k := k) (equivOfEq h) := by
  subst B
  exact A.identityGerm

/-- The corresponding boundary transport is also fixed by equality. -/
def boundaryOfEq {A B : OriginalNativeCompactModel k} (h : A = B) :
    (IntrinsicBoundary.smoothManifold k A.Point).SmoothEquiv
      (IntrinsicBoundary.smoothManifold k B.Point) := by
  subst B
  exact Diffeomorph.refl _ _ _

theorem boundaryOfEq_val {A B : OriginalNativeCompactModel k} (h : A = B)
    (x : IntrinsicBoundary.Point k A.Point) :
    (boundaryOfEq h x).val = equivOfEq h x.val := by
  subst B
  rfl

end OriginalNativeCompactModel

/-- The original compact geometric tuple, before any represented pair or
completion is chosen. Both full covector primitives and the witness occur. -/
structure OriginalPositiveCompactTuple (a k : ℕ) where
  ambient : OriginalNativeCompactModel a
  ribbon : OriginalNativeCompactModel k
  primitive : Form a ambient.Point 1
  ribbonPrimitive : Form k ribbon.Point 1
  embedding : ribbon.Point → IntrinsicBoundary.Point a ambient.Point
  witness : IntrinsicBoundary.Point a ambient.Point → ℝ

namespace OriginalPositiveCompactTuple
variable {a k : ℕ} {P Q : OriginalPositiveCompactTuple a k}

def ambientEquiv (h : P = Q) := OriginalNativeCompactModel.equivOfEq (congrArg ambient h)
def ribbonEquiv (h : P = Q) := OriginalNativeCompactModel.equivOfEq (congrArg ribbon h)
def boundaryEquiv (h : P = Q) := OriginalNativeCompactModel.boundaryOfEq (congrArg ambient h)

/-- Tuple equality implies strictness of the full ambient primitive. -/
theorem ambientPrimitive (h : P = Q) (x : P.ambient.Point) :
    (Q.primitive (ambientEquiv h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) (ambientEquiv h) x) = P.primitive x := by
  subst Q
  change (P.primitive x).compContinuousLinearMap (mfderiv _ _ id x) = _
  rw [mfderiv_id]
  rfl

/-- The full ribbon primitive agrees with scale one. -/
theorem ribbonPrimitive_eq (h : P = Q) (x : P.ribbon.Point) :
    (Q.ribbonPrimitive (ribbonEquiv h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) (ribbonEquiv h) x) = P.ribbonPrimitive x := by
  subst Q
  change (P.ribbonPrimitive x).compContinuousLinearMap (mfderiv _ _ id x) = _
  rw [mfderiv_id]
  rfl

/-- Equality retains every original ribbon point, rather than its core. -/
theorem ribbonSquare (h : P = Q) (x : P.ribbon.Point) :
    boundaryEquiv h (P.embedding x) = Q.embedding (ribbonEquiv h x) := by
  subst Q
  rfl

/-- The witnessing function also agrees on the entire boundary. -/
theorem witness_eq (h : P = Q) (x : IntrinsicBoundary.Point a P.ambient.Point) :
    Q.witness (boundaryEquiv h x) = P.witness x := by
  subst Q
  rfl

end OriginalPositiveCompactTuple

/-- Original compact charts at one actual endpoint. Neither a represented
tuple nor a completed identification occurs in this choice. -/
structure OriginalPositiveEndpointChart {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
    (E : OriginalPositiveEndpoint a k n) where
  cA : OriginalCompactChart (k := a) (M := E.bundle.A) (E := E.bundle.EA)
  hcA : E.parameter ∈ cA.val.baseSet
  cM : OriginalCompactChart (k := k) (M := E.bundle.M) (E := E.bundle.EM)
  hcM : E.parameter ∈ cM.val.baseSet

namespace OriginalPositiveEndpointChart
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {E : OriginalPositiveEndpoint a k n} (C : OriginalPositiveEndpointChart E)

/-- Bundle self-transition regularity supplies identity germs, so the tuple
does not strengthen the original geometric input. -/
def tuple : OriginalPositiveCompactTuple a k where
  ambient :=
    { Point := E.bundle.A
      identityGerm := by
        have h := isLocallyExtendibleNativeMap_coordChange C.cA.val C.cA.val
          C.cA.property C.cA.property ⟨C.hcA, C.hcA⟩
        simpa only [C.cA.val.coordChange_same C.hcA] using h }
  ribbon :=
    { Point := E.bundle.M
      identityGerm := by
        have h := isLocallyExtendibleNativeMap_coordChange C.cM.val C.cM.val
          C.cM.property C.cM.property ⟨C.hcM, C.hcM⟩
        simpa only [C.cM.val.coordChange_same C.hcM] using h }
  primitive := E.bundle.PA.form C.cA E.parameter
  ribbonPrimitive := E.bundle.PM.form C.cM E.parameter
  embedding := E.bundle.PJ.map C.cM C.cA E.parameter
  witness := E.bundle.PW.witness C.cA E.parameter

abbrev ambientFamily := E.bundle.LA.localCompletionFamily C.cA E.parameter C.hcA
abbrev ribbonFamily := E.bundle.LM.localCompletionFamily C.cM E.parameter C.hcM

end OriginalPositiveEndpointChart

namespace CompletedMaslovDimension

def point {d e : ℕ} (h : d = e) (X : CompleteLiouvilleManifold d)
    (x : X.manifold.Point) : (ambient h X).manifold.Point := by
  subst e
  exact x

theorem equiv_point {d e : ℕ} (h : d = e)
    (X Y : CompleteLiouvilleManifold d) (f : X.manifold.SmoothEquiv Y.manifold)
    (x : X.manifold.Point) : equiv h X Y f (point h X x) = point h Y (f x) := by
  subst e
  rfl

theorem equiv_primitive {d e : ℕ} (h : d = e)
    (X Y : CompleteLiouvilleManifold d) (f : X.manifold.SmoothEquiv Y.manifold)
    (hf : X.manifold.pullback Y.manifold f Y.primitive = X.primitive) :
    (ambient h X).manifold.pullback (ambient h Y).manifold (equiv h X Y f)
      (ambient h Y).primitive = (ambient h X).primitive := by
  subst e
  exact hf

theorem equiv_end {d e : ℕ} (h : d = e)
    {D D' : LiouvilleDomain d} (C : Completion D) (C' : Completion D')
    (f : C.ambient.manifold.SmoothEquiv C'.ambient.manifold)
    (x : D.domain.boundary.Point × ℝ) (y : D'.domain.boundary.Point × ℝ)
    (hf : f (C.endMap x) = C'.endMap y) :
    equiv h C.ambient C'.ambient f (endMap h C x) = endMap h C' y := by
  subst e
  exact hf

end CompletedMaslovDimension

section CompactAmbientMap
variable {a n : ℕ} [NeZero n]
  {A A' : Type} [TopologicalSpace A] [TopologicalSpace A']
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A']
  [IsManifold (𝓡∂ (a + 1)) ∞ A'] [CompactSpace A]
  {EA EA' : Parameter → Type} [∀ t, TopologicalSpace (EA t)]
  [∀ t, TopologicalSpace (EA' t)]
  [TopologicalSpace (TotalSpace A EA)] [TopologicalSpace (TotalSpace A' EA')]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A') EA']
  {PA : BundlePrimitiveData (k := a) (M := A) EA}
  {PA' : BundlePrimitiveData (k := a) (M := A') EA'}
  {c : OriginalCompactChart (k := a) (M := A) (E := EA)}
  {c' : OriginalCompactChart (k := a) (M := A') (E := EA')}
  {t t' : Parameter}

omit [NeZero n] in
/-- The original strict compact map extends to the independently retained
original local completions. Its boundary restriction and zero radial shift
are proved, rather than supplied as completion data. -/
theorem exists_originalAmbientJunction_of_compactMap
    (LA : OriginalBundleLiouvilleLaws PA) (LA' : OriginalBundleLiouvilleLaws PA')
    (U : LocalCompletionFamily PA c t) (V : LocalCompletionFamily PA' c' t')
    (s s' : Parameter) (hs : s ∈ U.base) (hs' : s' ∈ V.base)
    (hdim : a + 1 = 2 * n) (hdim' : a + 1 = 2 * n)
    (h : Diffeomorph (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) A A' ∞)
    (hgerm : IsLocallyExtendibleNativeMap (k := a) h)
    (hprimitive : ∀ x, (PA'.form c' s' (h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (a + 1)) (𝓡∂ (a + 1)) h x) = PA.form c s x)
    (bH : (IntrinsicBoundary.smoothManifold a A).SmoothEquiv
      (IntrinsicBoundary.smoothManifold a A'))
    (hboundary : ∀ x, (bH x).val = h x.val) :
    ∃ O : OriginalBundleAmbientJunction LA LA' U V s s' hdim hdim',
      O.ψ = bH ∧ O.shift = (fun _ => 0) ∧
      (∀ x, O.Ψ (CompletedMaslovDimension.point hdim (U.sliceCompletion LA s).ambient
        (IntrinsicCompletionGluing.original (U.native.patches s) x)) =
        CompletedMaslovDimension.point hdim' (V.sliceCompletion LA' s').ambient
          (IntrinsicCompletionGluing.original (V.native.patches s') (h x))) ∧
      ∀ x r, O.Ψ (CompletedMaslovDimension.endMap hdim (U.sliceCompletion LA s) (x, r)) =
        CompletedMaslovDimension.endMap hdim' (V.sliceCompletion LA' s') (bH x, r) := by
  obtain ⟨e, _, hp, hc, _, _, _⟩ :=
    (U.sliceNativePresentation LA s).exists_strictCompletionEquiv_of_nativeDiffeomorph
      (V.sliceNativePresentation LA' s') h hgerm
      (by simpa only [U.reparam_eq s hs, V.reparam_eq s' hs'] using hprimitive)
      (U.sliceCompletion LA s) (V.sliceCompletion LA' s')
  have he (x : A) : e (IntrinsicCompletionGluing.original (U.native.patches s) x) =
      IntrinsicCompletionGluing.original (V.native.patches s') (h x) := hc x
  have hflow := (U.sliceCompletion LA s).ambient.map_flow (V.sliceCompletion LA' s').ambient e hp
  have hend (x : IntrinsicBoundary.Point a A) (r : ℝ) :
      e ((U.sliceCompletion LA s).endMap (x, r)) =
        (V.sliceCompletion LA' s').endMap (bH x, r) := by
    rw [(U.sliceCompletion LA s).end_flow, (V.sliceCompletion LA' s').end_flow, hflow]
    congr 1
    change e ((IntrinsicCompletionGluing.compactDomain U.native.width_pos (U.native.collar s)
      (U.native.embedding s) (U.native.smooth s) (U.native.boundary s)
      (U.native.inverse s) (U.native.zero s)).boundaryInclusion.map x) =
      (IntrinsicCompletionGluing.compactDomain V.native.width_pos (V.native.collar s')
      (V.native.embedding s') (V.native.smooth s') (V.native.boundary s')
      (V.native.inverse s') (V.native.zero s')).boundaryInclusion.map (bH x)
    rw [IntrinsicCompletionGluing.compactDomain_boundaryInclusion,
      IntrinsicCompletionGluing.compactDomain_boundaryInclusion, he, hboundary]
  refine ⟨{
    Ψ := CompletedMaslovDimension.equiv hdim (U.sliceCompletion LA s).ambient
      (V.sliceCompletion LA' s').ambient e
    strictPrimitive := CompletedMaslovDimension.equiv_primitive hdim _ _ e hp
    ψ := bH
    shift := fun _ => 0
    smoothShift := contMDiff_const
    eventualEnd := ?_ }, rfl, rfl, ?_, ?_⟩
  · intro x
    refine ⟨0, fun r _ => ?_⟩
    simpa only [add_zero] using
      CompletedMaslovDimension.equiv_end hdim (U.sliceCompletion LA s)
        (V.sliceCompletion LA' s') e (x, r) (bH x, r) (hend x r)
  · intro x
    rw [CompletedMaslovDimension.equiv_point, he]
  · intro x r
    exact CompletedMaslovDimension.equiv_end hdim (U.sliceCompletion LA s)
      (V.sliceCompletion LA' s') e (x, r) (bH x, r) (hend x r)

end CompactAmbientMap

namespace OriginalPositiveEndpointChart
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {E : OriginalPositiveEndpoint a k n} (C : OriginalPositiveEndpointChart E)

/-- The already proved original-local comparison, retaining the endpoint
chosen for this bundle everywhere in the original finite graph. -/
def localComparison :
    (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.SmoothEquiv
      E.pair.ambientManifold :=
  let F := E.bundle.realize
  CompletedMaslovDimension.comparison E.bundle.hdimA
    (C.ambientFamily.sliceCompletion E.bundle.LA E.parameter).ambient E.pair.ambientManifold
    (C.ambientFamily.ambientEndpointSliceComparison E.bundle.LA F.cA F.heA F.hbaseA
      E.parameter C.ambientFamily.base_mem F.Q E.bundle.hdimA F.eAs F.hp F.hc).equiv

theorem localComparison_primitive :
    (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.pullback
      E.pair.ambientManifold C.localComparison E.pair.ambientCompletion.ambient.primitive =
        (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive := by
  let F := E.bundle.realize
  exact CompletedMaslovDimension.comparison_primitive E.bundle.hdimA
    (C.ambientFamily.sliceCompletion E.bundle.LA E.parameter).ambient E.pair.ambientManifold
    (C.ambientFamily.ambientEndpointSliceComparison E.bundle.LA F.cA F.heA F.hbaseA
      E.parameter C.ambientFamily.base_mem F.Q E.bundle.hdimA F.eAs F.hp F.hc).equiv _
    (C.ambientFamily.ambientEndpointSliceComparison E.bundle.LA F.cA F.heA F.hbaseA
      E.parameter C.ambientFamily.base_mem F.Q E.bundle.hdimA F.eAs F.hp F.hc).primitive

theorem localComparison_symplectic :
    (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative
      (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive =
    (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.pullback
      E.pair.ambientManifold C.localComparison
        (E.pair.ambientManifold.exteriorDerivative E.pair.ambientCompletion.ambient.primitive) := by
  rw [← C.localComparison_primitive]
  exact (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative_pullback
    E.pair.ambientManifold C.localComparison.toContMDiffMap _
    E.pair.ambientCompletion.ambient.smooth_primitive

/-- A smooth representative of the actual original local Maslov datum.
The recovery theorems below identify its fields with the independently
supplied original fields, so its class is an original endpoint class. -/
def originalMaslov : MaslovRepresentative
    (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold
    ((localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative
      (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive) :=
  E.maslov.pullbackTo C.localComparison C.localComparison_symplectic.symm

/-- Full original complex-structure recovery, on every completed point. -/
theorem originalMaslov_J : C.originalMaslov.J =
    E.bundle.S.J C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem := by
  let F := E.bundle.realize
  exact (E.bundle.S.pullback_maslovFamilyRepresentative_descended
    F.cA F.heA F.hbaseA F.Q F.eAs F.hp F.hc F.f F.familyJ F.familyTensor
    C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem).1

/-- Recovery of every slot of the original full canonical-square tensor. -/
theorem originalMaslov_tensor : C.originalMaslov.tensor =
    E.bundle.S.tensor C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem := by
  let F := E.bundle.realize
  exact (E.bundle.S.pullback_maslovFamilyRepresentative_descended
    F.cA F.heA F.hbaseA F.Q F.eAs F.hp F.hc F.f F.familyJ F.familyTensor
    C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem).2

/-- Every independently supplied representative with the original fields
is exactly this representative; its proofs introduce no further choice. -/
theorem originalMaslov_eq_of_fields
    (s : MaslovRepresentative
      (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold
      ((localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative
        (localMaslovAmbient E.bundle.hdimA E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive))
    (hJ : s.J = E.bundle.S.J C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem)
    (hT : s.tensor = E.bundle.S.tensor C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem) :
    s = C.originalMaslov :=
  MaslovRepresentative.ext (hJ.trans C.originalMaslov_J.symm)
    (hT.trans C.originalMaslov_tensor.symm)

end OriginalPositiveEndpointChart

namespace OriginalPositiveEndpointChart
variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {L R : OriginalPositiveEndpoint a k n}
  (C : OriginalPositiveEndpointChart L) (D : OriginalPositiveEndpointChart R)

/-- Equality of independently described original compact tuples produces
the original completed ambient junction, with canonical boundary and shift. -/
theorem exists_ambientNormalization (h : C.tuple = D.tuple) :
    ∃ O : OriginalBundleAmbientJunction L.bundle.LA R.bundle.LA
      C.ambientFamily D.ambientFamily L.parameter R.parameter
      L.bundle.hdimA R.bundle.hdimA,
      O.ψ = OriginalPositiveCompactTuple.boundaryEquiv h ∧ O.shift = (fun _ => 0) ∧
      (∀ x, O.Ψ (CompletedMaslovDimension.point L.bundle.hdimA
        (C.ambientFamily.sliceCompletion L.bundle.LA L.parameter).ambient
        (IntrinsicCompletionGluing.original (C.ambientFamily.native.patches L.parameter) x)) =
        CompletedMaslovDimension.point R.bundle.hdimA
          (D.ambientFamily.sliceCompletion R.bundle.LA R.parameter).ambient
          (IntrinsicCompletionGluing.original (D.ambientFamily.native.patches R.parameter)
            (OriginalPositiveCompactTuple.ambientEquiv h x))) ∧
      ∀ x r, O.Ψ (CompletedMaslovDimension.endMap L.bundle.hdimA
        (C.ambientFamily.sliceCompletion L.bundle.LA L.parameter) (x, r)) =
        CompletedMaslovDimension.endMap R.bundle.hdimA
          (D.ambientFamily.sliceCompletion R.bundle.LA R.parameter)
          (OriginalPositiveCompactTuple.boundaryEquiv h x, r) := by
  exact exists_originalAmbientJunction_of_compactMap L.bundle.LA R.bundle.LA
    C.ambientFamily D.ambientFamily L.parameter R.parameter
    C.ambientFamily.base_mem D.ambientFamily.base_mem L.bundle.hdimA R.bundle.hdimA
    (OriginalPositiveCompactTuple.ambientEquiv h)
    (OriginalNativeCompactModel.equivOfEq_germ (congrArg OriginalPositiveCompactTuple.ambient h))
    (OriginalPositiveCompactTuple.ambientPrimitive h)
    (OriginalPositiveCompactTuple.boundaryEquiv h)
    (OriginalNativeCompactModel.boundaryOfEq_val (congrArg OriginalPositiveCompactTuple.ambient h))

/-- A specified choice of the produced strict extension; it is independent
of every represented pair realization. -/
def ambientNormalization (h : C.tuple = D.tuple) :
    OriginalBundleAmbientJunction L.bundle.LA R.bundle.LA
      C.ambientFamily D.ambientFamily L.parameter R.parameter
      L.bundle.hdimA R.bundle.hdimA :=
  Classical.choose (C.exists_ambientNormalization D h)

theorem ambientNormalization_boundary (h : C.tuple = D.tuple) :
    (C.ambientNormalization D h).ψ = OriginalPositiveCompactTuple.boundaryEquiv h :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).1

theorem ambientNormalization_shift (h : C.tuple = D.tuple) :
    (C.ambientNormalization D h).shift = (fun _ => 0) :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).2.1

theorem ambientNormalization_compact (h : C.tuple = D.tuple) (x : L.bundle.A) :
    (C.ambientNormalization D h).Ψ (CompletedMaslovDimension.point L.bundle.hdimA
      (C.ambientFamily.sliceCompletion L.bundle.LA L.parameter).ambient
      (IntrinsicCompletionGluing.original (C.ambientFamily.native.patches L.parameter) x)) =
      CompletedMaslovDimension.point R.bundle.hdimA
        (D.ambientFamily.sliceCompletion R.bundle.LA R.parameter).ambient
        (IntrinsicCompletionGluing.original (D.ambientFamily.native.patches R.parameter)
          (OriginalPositiveCompactTuple.ambientEquiv h x)) :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).2.2.1 x

theorem ambientNormalization_end (h : C.tuple = D.tuple)
    (x : IntrinsicBoundary.Point a L.bundle.A) (r : ℝ) :
    (C.ambientNormalization D h).Ψ (CompletedMaslovDimension.endMap L.bundle.hdimA
      (C.ambientFamily.sliceCompletion L.bundle.LA L.parameter) (x, r)) =
      CompletedMaslovDimension.endMap R.bundle.hdimA
        (D.ambientFamily.sliceCompletion R.bundle.LA R.parameter)
        (OriginalPositiveCompactTuple.boundaryEquiv h x, r) :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).2.2.2 x r

/-- Agreement of the two original endpoint classes under the strict
extension constructed from compact tuple equality. No homotopy, represented
grading or junction is part of this proposition. -/
def ClassesAgree (h : C.tuple = D.tuple) : Prop :=
  Quot.mk MaslovHomotopic C.originalMaslov =
    Quot.mk MaslovHomotopic (D.originalMaslov.pullbackTo
      (C.ambientNormalization D h).Ψ (C.ambientNormalization D h).strictSymplectic.symm)

/-- The class premise can be stated using arbitrary independently supplied
original representatives. It imposes no realization-dependent requirement. -/
theorem classesAgree_iff_originalRepresentatives (h : C.tuple = D.tuple)
    (s : MaslovRepresentative _ _) (t : MaslovRepresentative _ _)
    (hJs : s.J = L.bundle.S.J C.cA L.parameter C.hcA L.parameter C.ambientFamily.base_mem)
    (hTs : s.tensor = L.bundle.S.tensor C.cA L.parameter C.hcA L.parameter C.ambientFamily.base_mem)
    (hJt : t.J = R.bundle.S.J D.cA R.parameter D.hcA R.parameter D.ambientFamily.base_mem)
    (hTt : t.tensor = R.bundle.S.tensor D.cA R.parameter D.hcA R.parameter D.ambientFamily.base_mem) :
    C.ClassesAgree D h ↔ Quot.mk MaslovHomotopic s =
      Quot.mk MaslovHomotopic (t.pullbackTo (C.ambientNormalization D h).Ψ
        (C.ambientNormalization D h).strictSymplectic.symm) := by
  rw [C.originalMaslov_eq_of_fields s hJs hTs, D.originalMaslov_eq_of_fields t hJt hTt]
  rfl

/-- Compact equality produces the geometric junction. Equality of original
classes supplies its smooth homotopy through the proved quotient criterion. -/
def normalizedJunction (h : C.tuple = D.tuple) (hg : C.ClassesAgree D h) :
    OriginalPositiveJunction L R where
  cA := C.cA
  cA' := D.cA
  t := L.parameter
  t' := R.parameter
  ht := C.hcA
  ht' := D.hcA
  hs := C.ambientFamily.base_mem
  hs' := D.ambientFamily.base_mem
  ambient := C.ambientNormalization D h
  cM := C.cM
  cM' := D.cM
  tM := L.parameter
  tM' := R.parameter
  htM := C.hcM
  htM' := D.hcM
  hsM := C.ribbonFamily.base_mem
  hsM' := D.ribbonFamily.base_mem
  ribbon := OriginalPositiveCompactTuple.ribbonEquiv h
  ribbonGerm := OriginalNativeCompactModel.equivOfEq_germ (congrArg OriginalPositiveCompactTuple.ribbon h)
  scale := 1
  positiveScale := zero_lt_one
  primitiveScale := by
    intro x
    rw [one_smul]
    exact OriginalPositiveCompactTuple.ribbonPrimitive_eq h x
  ribbonSquare := by
    rw [C.ambientNormalization_boundary D h]
    exact OriginalPositiveCompactTuple.ribbonSquare h
  nativeSource := C.originalMaslov
  nativeTarget := D.originalMaslov
  sourceJ := C.originalMaslov_J
  sourceTensor := C.originalMaslov_tensor
  targetJ := D.originalMaslov_J
  targetTensor := D.originalMaslov_tensor
  homotopy := Classical.choice ((MaslovClass.eq_iff_homotopic _ _).mp hg)

/-- The equality-normalized arrow can be used directly by the existing
finite original-bundle compiler, which retains this exact graded lift. -/
def normalizationStep (h : C.tuple = D.tuple) (hg : C.ClassesAgree D h) :
    OriginalPositiveStep a k n L R := .junction (C.normalizedJunction D h hg)

/-- A supplied finite itinerary can append an equal independently described
endpoint without supplying any original junction as additional data. -/
theorem exists_gradedChain_append_normalization
    {A : OriginalPositiveEndpoint a k n} (p : Quiver.Path A L)
    (h : C.tuple = D.tuple) (hg : C.ClassesAgree D h) :
    ∃ chain : ComparisonChain A.pair R.pair,
      chain = OriginalPositiveEndpoint.comparisonChain (p.cons (C.normalizationStep D h hg)) ∧
      chain.length = p.length + 1 ∧
      chain.vertices = (p.vertices.concat R).map OriginalPositiveEndpoint.pair ∧
      Nonempty (GradedComparisonChain A.pair chain A.maslov R.maslov) := by
  refine ⟨OriginalPositiveEndpoint.comparisonChain (p.cons (C.normalizationStep D h hg)),
    rfl, ?_, ?_, ⟨OriginalPositiveEndpoint.gradedChain (p.cons (C.normalizationStep D h hg))⟩⟩
  · exact OriginalPositiveEndpoint.comparisonChain_length _
  · exact OriginalPositiveEndpoint.comparisonChain_vertices _

end OriginalPositiveEndpointChart

end FsFltz.Geometry.IntrinsicSmoothBundle
