import FsFltz.Geometry.OriginalBundleEqualEndpointNormalization

/-!
# Equal original endpoint normalization with zero-dimensional ribbons

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–199;
`def:maslov`, lines 212–244; `thm:target`, lines 352–415; and
`sec:lean`, lines 766–836. The zero-dimensional ribbon may be empty.
Equality of the full original compact tuple constructs its original strict
completion junction, and original Maslov class agreement supplies its grade.
These are conditional foundations; the geometric target remains unproved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville FsFltz.Geometry.IntrinsicZeroLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- The literal original compact zero-dimensional manifold. Empty carriers
are permitted, and no boundary germ is needed for its maps. -/
structure OriginalZeroCompactModel where
  Point : Type
  [topology : TopologicalSpace Point]
  [separated : T2Space Point]
  [countable : SecondCountableTopology Point]
  [compact : CompactSpace Point]
  [charted : ChartedSpace (Model 0) Point]
  [manifold : IsManifold 𝓘(ℝ, Model 0) ∞ Point]

attribute [instance] OriginalZeroCompactModel.topology OriginalZeroCompactModel.separated
  OriginalZeroCompactModel.countable OriginalZeroCompactModel.compact
  OriginalZeroCompactModel.charted OriginalZeroCompactModel.manifold

def OriginalZeroCompactModel.equivOfEq {A B : OriginalZeroCompactModel} (h : A = B) :
    Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) A.Point B.Point ∞ := by
  subst B
  exact Diffeomorph.refl _ _ _

/-- Original ambient and entire finite ribbon geometry at a parameter. -/
structure OriginalZeroCompactTuple where
  ambient : OriginalNativeCompactModel 1
  ribbon : OriginalZeroCompactModel
  primitive : Form 1 ambient.Point 1
  ribbonPrimitive : (sourceManifold ribbon.Point).Form 1
  embedding : ribbon.Point → IntrinsicBoundary.Point 1 ambient.Point
  witness : IntrinsicBoundary.Point 1 ambient.Point → ℝ

namespace OriginalZeroCompactTuple
variable {P Q : OriginalZeroCompactTuple}

def ambientEquiv (h : P = Q) := OriginalNativeCompactModel.equivOfEq (congrArg ambient h)
def ribbonEquiv (h : P = Q) := OriginalZeroCompactModel.equivOfEq (congrArg ribbon h)
def boundaryEquiv (h : P = Q) := OriginalNativeCompactModel.boundaryOfEq (congrArg ambient h)

theorem ambientPrimitive (h : P = Q) (x : P.ambient.Point) :
    (Q.primitive (ambientEquiv h x)).compContinuousLinearMap
      (mfderiv (𝓡∂ 2) (𝓡∂ 2) (ambientEquiv h) x) = P.primitive x := by
  subst Q
  change (P.primitive x).compContinuousLinearMap (mfderiv _ _ id x) = _
  rw [mfderiv_id]
  rfl

theorem ribbonSquare (h : P = Q) (x : P.ribbon.Point) :
    boundaryEquiv h (P.embedding x) = Q.embedding (ribbonEquiv h x) := by
  subst Q
  rfl

theorem witness_eq (h : P = Q) (x : IntrinsicBoundary.Point 1 P.ambient.Point) :
    Q.witness (boundaryEquiv h x) = P.witness x := by
  subst Q
  rfl

end OriginalZeroCompactTuple

/-- Original compact charts at an actual zero-ribbon endpoint. -/
structure OriginalZeroEndpointChart (E : OriginalZeroEndpoint) where
  cA : OriginalCompactChart (k := 1) (M := E.bundle.A) (E := E.bundle.EA)
  hcA : E.parameter ∈ cA.val.baseSet
  cM : OriginalZeroCompactChart (M := E.bundle.M) (E := E.bundle.EM)
  hcM : E.parameter ∈ cM.val.baseSet

namespace OriginalZeroEndpointChart
variable {E : OriginalZeroEndpoint} (C : OriginalZeroEndpointChart E)

/-- The whole original tuple, with ambient identity germs derived from the
actual bundle self-transition. It contains no represented realization. -/
def tuple : OriginalZeroCompactTuple where
  ambient :=
    { Point := E.bundle.A
      identityGerm := by
        have h := isLocallyExtendibleNativeMap_coordChange C.cA.val C.cA.val
          C.cA.property C.cA.property ⟨C.hcA, C.hcA⟩
        simpa only [C.cA.val.coordChange_same C.hcA] using h }
  ribbon := { Point := E.bundle.M }
  primitive := E.bundle.PA.form C.cA E.parameter
  ribbonPrimitive := E.bundle.μ E.parameter
  embedding := E.bundle.PJ.map C.cM C.cA E.parameter
  witness := E.bundle.PW.witness C.cA E.parameter

abbrev ambientFamily := E.bundle.LA.localCompletionFamily C.cA E.parameter C.hcA

def localComparison :
    (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.SmoothEquiv
      E.pair.ambientManifold :=
  let F := E.bundle.realize
  CompletedMaslovDimension.comparison rfl
    (C.ambientFamily.sliceCompletion E.bundle.LA E.parameter).ambient E.pair.ambientManifold
    (C.ambientFamily.ambientEndpointSliceComparison E.bundle.LA F.eA F.heA F.hbaseA
      E.parameter C.ambientFamily.base_mem F.Q rfl F.eAs F.hp F.hc).equiv

theorem localComparison_primitive :
    (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.pullback
      E.pair.ambientManifold C.localComparison E.pair.ambientCompletion.ambient.primitive =
        (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive := by
  let F := E.bundle.realize
  exact CompletedMaslovDimension.comparison_primitive rfl
    (C.ambientFamily.sliceCompletion E.bundle.LA E.parameter).ambient E.pair.ambientManifold
    (C.ambientFamily.ambientEndpointSliceComparison E.bundle.LA F.eA F.heA F.hbaseA
      E.parameter C.ambientFamily.base_mem F.Q rfl F.eAs F.hp F.hc).equiv _
    (C.ambientFamily.ambientEndpointSliceComparison E.bundle.LA F.eA F.heA F.hbaseA
      E.parameter C.ambientFamily.base_mem F.Q rfl F.eAs F.hp F.hc).primitive

theorem localComparison_symplectic :
    (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative
      (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive =
    (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.pullback
      E.pair.ambientManifold C.localComparison
        (E.pair.ambientManifold.exteriorDerivative E.pair.ambientCompletion.ambient.primitive) := by
  rw [← C.localComparison_primitive]
  exact (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative_pullback
    E.pair.ambientManifold C.localComparison.toContMDiffMap _
    E.pair.ambientCompletion.ambient.smooth_primitive

/-- A representative of the actual original completed local datum. -/
def originalMaslov : MaslovRepresentative
    (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold
    ((localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative
      (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive) :=
  E.maslov.pullbackTo C.localComparison C.localComparison_symplectic.symm

theorem originalMaslov_J : C.originalMaslov.J =
    E.bundle.S.J C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem := by
  let F := E.bundle.realize
  exact (E.bundle.S.pullback_maslovFamilyRepresentative_descended
    F.eA F.heA F.hbaseA F.Q F.eAs F.hp F.hc F.f F.familyJ F.familyTensor
    C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem).1

theorem originalMaslov_tensor : C.originalMaslov.tensor =
    E.bundle.S.tensor C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem := by
  let F := E.bundle.realize
  exact (E.bundle.S.pullback_maslovFamilyRepresentative_descended
    F.eA F.heA F.hbaseA F.Q F.eAs F.hp F.hc F.f F.familyJ F.familyTensor
    C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem).2

theorem originalMaslov_eq_of_fields
    (s : MaslovRepresentative
      (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold
      ((localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).manifold.exteriorDerivative
        (localMaslovAmbient (n := 1) rfl E.bundle.LA C.cA E.parameter C.hcA E.parameter).primitive))
    (hJ : s.J = E.bundle.S.J C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem)
    (hT : s.tensor = E.bundle.S.tensor C.cA E.parameter C.hcA E.parameter C.ambientFamily.base_mem) :
    s = C.originalMaslov :=
  MaslovRepresentative.ext (hJ.trans C.originalMaslov_J.symm)
    (hT.trans C.originalMaslov_tensor.symm)

end OriginalZeroEndpointChart

namespace OriginalZeroEndpointChart
variable {L R : OriginalZeroEndpoint}
  (C : OriginalZeroEndpointChart L) (D : OriginalZeroEndpointChart R)

/-- Independent original tuples construct the strict completion map,
retaining all compact points and every real-radius boundary orbit. -/
theorem exists_ambientNormalization (h : C.tuple = D.tuple) :
    ∃ O : OriginalBundleAmbientJunction L.bundle.LA R.bundle.LA
      C.ambientFamily D.ambientFamily L.parameter R.parameter (n := 1) rfl rfl,
      O.ψ = OriginalZeroCompactTuple.boundaryEquiv h ∧ O.shift = (fun _ => 0) ∧
      (∀ x, O.Ψ (IntrinsicCompletionGluing.original (C.ambientFamily.native.patches L.parameter) x) =
        IntrinsicCompletionGluing.original (D.ambientFamily.native.patches R.parameter)
          (OriginalZeroCompactTuple.ambientEquiv h x)) ∧
      ∀ x r, O.Ψ ((C.ambientFamily.sliceCompletion L.bundle.LA L.parameter).endMap (x, r)) =
        (D.ambientFamily.sliceCompletion R.bundle.LA R.parameter).endMap
          (OriginalZeroCompactTuple.boundaryEquiv h x, r) := by
  exact exists_originalAmbientJunction_of_compactMap L.bundle.LA R.bundle.LA
    C.ambientFamily D.ambientFamily L.parameter R.parameter
    C.ambientFamily.base_mem D.ambientFamily.base_mem (n := 1) rfl rfl
    (OriginalZeroCompactTuple.ambientEquiv h)
    (OriginalNativeCompactModel.equivOfEq_germ (congrArg OriginalZeroCompactTuple.ambient h))
    (OriginalZeroCompactTuple.ambientPrimitive h)
    (OriginalZeroCompactTuple.boundaryEquiv h)
    (OriginalNativeCompactModel.boundaryOfEq_val (congrArg OriginalZeroCompactTuple.ambient h))

def ambientNormalization (h : C.tuple = D.tuple) :
    OriginalBundleAmbientJunction L.bundle.LA R.bundle.LA
      C.ambientFamily D.ambientFamily L.parameter R.parameter (n := 1) rfl rfl :=
  Classical.choose (C.exists_ambientNormalization D h)

theorem ambientNormalization_boundary (h : C.tuple = D.tuple) :
    (C.ambientNormalization D h).ψ = OriginalZeroCompactTuple.boundaryEquiv h :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).1

theorem ambientNormalization_shift (h : C.tuple = D.tuple) :
    (C.ambientNormalization D h).shift = (fun _ => 0) :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).2.1

theorem ambientNormalization_compact (h : C.tuple = D.tuple) (x : L.bundle.A) :
    (C.ambientNormalization D h).Ψ
      (IntrinsicCompletionGluing.original (C.ambientFamily.native.patches L.parameter) x) =
      IntrinsicCompletionGluing.original (D.ambientFamily.native.patches R.parameter)
        (OriginalZeroCompactTuple.ambientEquiv h x) :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).2.2.1 x

theorem ambientNormalization_end (h : C.tuple = D.tuple)
    (x : IntrinsicBoundary.Point 1 L.bundle.A) (r : ℝ) :
    (C.ambientNormalization D h).Ψ
      ((C.ambientFamily.sliceCompletion L.bundle.LA L.parameter).endMap (x, r)) =
      (D.ambientFamily.sliceCompletion R.bundle.LA R.parameter).endMap
        (OriginalZeroCompactTuple.boundaryEquiv h x, r) :=
  (Classical.choose_spec (C.exists_ambientNormalization D h)).2.2.2 x r

def ClassesAgree (h : C.tuple = D.tuple) : Prop :=
  Quot.mk MaslovHomotopic C.originalMaslov =
    Quot.mk MaslovHomotopic (D.originalMaslov.pullbackTo
      (C.ambientNormalization D h).Ψ (C.ambientNormalization D h).strictSymplectic.symm)

/-- Independently supplied original representatives give the same class
premise, including the empty zero-ribbon case. -/
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

/-- The entire zero-ribbon junction is derived from tuple equality and
original class equality. Empty ribbons require no additional hypothesis. -/
def normalizedJunction (h : C.tuple = D.tuple) (hg : C.ClassesAgree D h) :
    OriginalZeroJunction L R where
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
  hsM := C.hcM
  hsM' := D.hcM
  ribbon := OriginalZeroCompactTuple.ribbonEquiv h
  scale := 1
  positiveScale := zero_lt_one
  ribbonSquare := by
    rw [C.ambientNormalization_boundary D h]
    exact OriginalZeroCompactTuple.ribbonSquare h
  nativeSource := C.originalMaslov
  nativeTarget := D.originalMaslov
  sourceJ := C.originalMaslov_J
  sourceTensor := C.originalMaslov_tensor
  targetJ := D.originalMaslov_J
  targetTensor := D.originalMaslov_tensor
  homotopy := Classical.choice ((MaslovClass.eq_iff_homotopic _ _).mp hg)

def normalizationStep (h : C.tuple = D.tuple) (hg : C.ClassesAgree D h) :
    OriginalZeroStep L R := .junction (C.normalizedJunction D h hg)

/-- The old finite compiler consumes the equality-produced junction and
grades the same literal path, including the empty input path. -/
theorem exists_gradedChain_append_normalization
    {A : OriginalZeroEndpoint} (p : Quiver.Path A L)
    (h : C.tuple = D.tuple) (hg : C.ClassesAgree D h) :
    ∃ chain : ComparisonChain A.pair R.pair,
      chain = OriginalZeroEndpoint.comparisonChain (p.cons (C.normalizationStep D h hg)) ∧
      chain.length = p.length + 1 ∧
      chain.vertices = (p.vertices.concat R).map OriginalZeroEndpoint.pair ∧
      Nonempty (GradedComparisonChain A.pair chain A.maslov R.maslov) := by
  refine ⟨OriginalZeroEndpoint.comparisonChain (p.cons (C.normalizationStep D h hg)),
    rfl, ?_, ?_, ⟨OriginalZeroEndpoint.gradedChain (p.cons (C.normalizationStep D h hg))⟩⟩
  · exact OriginalZeroEndpoint.comparisonChain_length _
  · exact OriginalZeroEndpoint.comparisonChain_vertices _

end OriginalZeroEndpointChart

end FsFltz.Geometry.IntrinsicSmoothBundle
