import FsFltz.Geometry.OriginalBundleMaslovSourceRegularity
import FsFltz.Geometry.OriginalBundleCompletionMarkingFieldRegularity
import FsFltz.Geometry.OriginalBundleMaslovSectionPullback
import FsFltz.Geometry.OriginalBundleFiniteRealization

/-!
# Original realizations from an independently smooth completed source

Source: `geoemtric-part-fsf.tex`, `def:chain` (163–199), `def:maslov`
(212–244), both markings in `g:initial` (374–384), and `sec:lean`
(788–814). The completed sources and their inclusion markings are prescribed
independently. A fixed smooth presentation carries varying primitives and
symplectic forms together with a smooth Maslov family. Ordinary smoothness
of the transported primitives produces the source-field and finite-flow
germs. With the smooth compact source inclusion these yield the actual
marking-map germs, then the full tensor and coframe germs consumed by the
existing original realizations. The flow-germ variants expose the same route
at an intermediate stage.

Only actual interval parameters carry geometric laws. Real local extensions
do not require complete off-interval sources. The general completed-family
correspondence and the target geometric existence theorem remain pending;
no represented or graded pair deformation is an input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- The supplied smooth family determines the representative on each
independent completed source through its actual smooth presentation. -/
def smoothSourceMaslovRepresentative {n : ℕ}
    (Z : Parameter → CompleteLiouvilleManifold (2 * n))
    (N : SmoothManifold (2 * n)) (η : ℝ → N.Form 2) (f : MaslovFamily N η)
    (R : ∀ s, (Z s).manifold.SmoothEquiv N)
    (hη : ∀ s, (Z s).manifold.pullback N (R s) (η s.val) =
      (Z s).manifold.exteriorDerivative (Z s).primitive)
    (s : Parameter) : MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive) :=
  (f.representative s).pullbackTo (R s) (hη s)

section SourceRegularity

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P}
  (hdim : k + 1 = 2 * n)
  (Z : Parameter → CompleteLiouvilleManifold (2 * n))
  (O : OriginalBundleCompletionMarkingData L Z)
  (N : SmoothManifold (2 * n)) (η : ℝ → N.Form 2) (f : MaslovFamily N η)
  (R : ∀ s, (Z s).manifold.SmoothEquiv N)
  (hη : ∀ s, (Z s).manifold.pullback N (R s) (η s.val) =
    (Z s).manifold.exteriorDerivative (Z s).primitive)

namespace OriginalBundleCompletionMarkingData

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Contravariance identifies the original pulled field with the pullback
along the literal composite marking, after dimension reindexing. -/
theorem smoothSource_originalJ
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (O.originalMaslovData hdim (smoothSourceMaslovRepresentative Z N η f R hη)).J c t ht s hs =
      pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold N
        (CompletedMaslovDimension.comparison hdim
          ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient N
          ((O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s)))
        (f.J s.val) := by
  rw [O.originalMaslovData_J]
  change pullbackAlmostComplex _ _ _ (pullbackAlmostComplex _ _ _ (f.J s.val)) = _
  rw [← pullbackAlmostComplex_trans]
  rw [localMaslovEquiv, CompletedMaslovDimension.comparison_trans]

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The same actual composite recovers every slot of the full source tensor. -/
theorem smoothSource_originalTensor
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (O.originalMaslovData hdim (smoothSourceMaslovRepresentative Z N η f R hη)).tensor c t ht s hs =
      pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold N
        (CompletedMaslovDimension.comparison hdim
          ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient N
          ((O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s)))
        (f.tensor s.val) := by
  rw [O.originalMaslovData_tensor]
  change pullbackSquaredTensor _ _ _ (pullbackSquaredTensor _ _ _ (f.tensor s.val)) = _
  rw [← pullbackSquaredTensor_trans]
  rw [localMaslovEquiv, CompletedMaslovDimension.comparison_trans]

variable
  (hi : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := L.localCompletionFamily c t ht
    HasSmoothTargetFamilyOn (𝓡∂ (k + 1)) N F.base
      (fun s x => R s (chartValue c.val (O.compact s) s x)))
  (hflow : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    HasRealSmoothFlowGermsOn N (L.localCompletionFamily c t ht).base
      (fun s r y => R s ((Z s).completeFlow.flow r ((R s).symm y))))

include hi hflow in
/-- Smooth source fields and full tensors pass through the actual source
inclusion and flow to all original charts. Both marking-map regularity and
pullback identities are derived; desired tensor or coframe germs are not inputs. -/
theorem tensorGerms_of_smooth_source_flow :
    OriginalLocalCompletionMaslovTensorGerms
      (O.originalMaslovData hdim (smoothSourceMaslovRepresentative Z N η f R hη)) := by
  apply OriginalLocalCompletionMaslovData.tensorGerms_of_markingMapGerms
    (O.originalMaslovData hdim (smoothSourceMaslovRepresentative Z N η f R hη)) N η f
    (fun c t ht s hs => (O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s))
  · exact O.smoothSource_originalJ hdim Z N η f R hη
  · exact O.smoothSource_originalTensor hdim Z N η f R hη
  · intro c t ht
    exact (O.localEquiv_realGerms_of_source_inclusion_and_flow
      (L.localCompletionFamily c t ht) N R (hi c t ht) (hflow c t ht)).1
  · intro c t ht
    exact (O.localEquiv_realGerms_of_source_inclusion_and_flow
      (L.localCompletionFamily c t ht) N R (hi c t ht) (hflow c t ht)).2

variable (hα : N.IsSmoothIntervalFormFamily
  (fun s => N.pullback (Z s).manifold (R s).symm (Z s).primitive))

include hi hα in
/-- Ordinary smoothness of the varying transported source primitives
produces the actual flow germs, marking germs and full pulled tensor germs.
No family-field, flow or marking-map germ is assumed. -/
theorem tensorGerms_of_smooth_source :
    OriginalLocalCompletionMaslovTensorGerms
      (O.originalMaslovData hdim (smoothSourceMaslovRepresentative Z N η f R hη)) := by
  apply OriginalLocalCompletionMaslovData.tensorGerms_of_markingMapGerms
    (O.originalMaslovData hdim (smoothSourceMaslovRepresentative Z N η f R hη)) N η f
    (fun c t ht s hs => (O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s))
  · exact O.smoothSource_originalJ hdim Z N η f R hη
  · exact O.smoothSource_originalTensor hdim Z N η f R hη
  · intro c t ht
    exact (O.localEquiv_realGerms_of_source_inclusion_and_primitive_smooth
      (L.localCompletionFamily c t ht) N R (hi c t ht) hα).1
  · intro c t ht
    exact (O.localEquiv_realGerms_of_source_inclusion_and_primitive_smooth
      (L.localCompletionFamily c t ht) N R (hi c t ht) hα).2

end OriginalBundleCompletionMarkingData
end SourceRegularity

section PositiveRibbon

variable {a k n : ℕ} [NeZero n] [NeZero (2 * n - 2)]
  {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace (a + 1)) A] [IsManifold (𝓡∂ (a + 1)) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M] [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {EA : Parameter → Type} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ (a + 1)) (F := A) EA]
  {EM : Parameter → Type} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) EM]
  (hdimA : a + 1 = 2 * n) (hdimM : k + 1 = 2 * n - 2)
  (PA : BundlePrimitiveData (k := a) (M := A) EA)
  (PM : BundlePrimitiveData (k := k) (M := M) EM)
  (PW : BundleWitnessData (k := a) (M := A) EA)
  (PJ : BundleRibbonData (a := a) (M := M) (A := A) (𝓡∂ (k + 1)) EM EA)
  (LA : OriginalBundleLiouvilleLaws PA) (LM : OriginalBundleLiouvilleLaws PM)
  (LP : OriginalBundlePairLaws PA PM PW PJ)
  (Z : Parameter → CompleteLiouvilleManifold (2 * n))
  (O : OriginalBundleCompletionMarkingData LA Z)
  (N : SmoothManifold (2 * n)) (η : ℝ → N.Form 2) (f : MaslovFamily N η)
  (R : ∀ s, (Z s).manifold.SmoothEquiv N)
  (hη : ∀ s, (Z s).manifold.pullback N (R s) (η s.val) =
    (Z s).manifold.exteriorDerivative (Z s).primitive)

variable
  (hi : ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasSmoothTargetFamilyOn (𝓡∂ (a + 1)) N F.base
      (fun s x => R s (chartValue c.val (O.compact s) s x)))
  (hflow : ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    HasRealSmoothFlowGermsOn N (LA.localCompletionFamily c t ht).base
      (fun s r y => R s ((Z s).completeFlow.flow r ((R s).symm y))))

/-- Construct the existing original positive-ribbon bundle. The two Maslov
fields are exactly the pullbacks of the supplied representative; covariance
and all coframe/scalar germs are proved before the realization is selected. -/
def smoothSourceFlowPositiveBundle : OriginalPositiveBundle a k n where
  A := A
  M := M
  EA := EA
  EM := EM
  hdimA := hdimA
  hdimM := hdimM
  PA := PA
  PM := PM
  PW := PW
  PJ := PJ
  LA := LA
  LM := LM
  LP := LP
  S := O.originalMaslovData hdimA (smoothSourceMaslovRepresentative Z N η f R hη)
  hS := (O.tensorGerms_of_smooth_source_flow hdimA Z N η f R hη hi hflow).coframeGerms

/-- The existing full realization consumes the generated original data and
coframe germs. Its geometry, grade and both marking-recovery capabilities
are retained in the complete existing realization type. -/
def smoothSourceFlowPositiveRealization :
    OriginalPositiveRealization
      (smoothSourceFlowPositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O N η f R hη hi hflow) :=
  (smoothSourceFlowPositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O N η f R hη hi hflow).realize


variable (hα : N.IsSmoothIntervalFormFamily
  (fun s => N.pullback (Z s).manifold (R s).symm (Z s).primitive))

/-- Ordinary smooth source primitives and compact inclusions produce the
original positive-ribbon bundle, including all required coframe germs. -/
def smoothSourcePositiveBundle : OriginalPositiveBundle a k n where
  A := A
  M := M
  EA := EA
  EM := EM
  hdimA := hdimA
  hdimM := hdimM
  PA := PA
  PM := PM
  PW := PW
  PJ := PJ
  LA := LA
  LM := LM
  LP := LP
  S := O.originalMaslovData hdimA (smoothSourceMaslovRepresentative Z N η f R hη)
  hS := (O.tensorGerms_of_smooth_source hdimA Z N η f R hη hi hα).coframeGerms

/-- The existing full realization consumes the generated original data and
coframe germs. Its geometry, grade and both marking-recovery capabilities
are retained in the complete existing realization type. -/
def smoothSourcePositiveRealization :
    OriginalPositiveRealization
      (smoothSourcePositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O N η f R hη hi hα) :=
  (smoothSourcePositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O N η f R hη hi hα).realize

end PositiveRibbon

section ZeroRibbon

variable {A M : Type} [TopologicalSpace A] [T2Space A] [SecondCountableTopology A] [CompactSpace A]
  [ChartedSpace (EuclideanHalfSpace 2) A] [IsManifold (𝓡∂ 2) ∞ A]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {EA : Parameter → Type} [∀ t, TopologicalSpace (EA t)]
  [TopologicalSpace (TotalSpace A EA)] [SmoothCompactBundle (𝓡∂ 2) (F := A) EA]
  {EM : Parameter → Type} [∀ t, TopologicalSpace (EM t)]
  [TopologicalSpace (TotalSpace M EM)] [SmoothCompactBundle 𝓘(ℝ, Model 0) (F := M) EM]
  (PA : BundlePrimitiveData (k := 1) (M := A) EA)
  (PW : BundleWitnessData (k := 1) (M := A) EA)
  (PJ : BundleRibbonData (a := 1) (M := M) (A := A) 𝓘(ℝ, Model 0) EM EA)
  (LA : OriginalBundleLiouvilleLaws PA)
  (hPJ : ∀ cM cA t, t ∈ cM.val.baseSet ∩ cA.val.baseSet → Function.Injective (PJ.map cM cA t))
  (μ : Parameter → (sourceManifold M).Form 1)
  (Z : Parameter → CompleteLiouvilleManifold 2)
  (O : OriginalBundleCompletionMarkingData LA Z)
  (N : SmoothManifold (2 * 1)) (η : ℝ → N.Form 2) (f : MaslovFamily N η)
  (R : ∀ s, (Z s).manifold.SmoothEquiv N)
  (hη : ∀ s, (Z s).manifold.pullback N (R s) (η s.val) =
    (Z s).manifold.exteriorDerivative (Z s).primitive)

variable
  (hi : ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    let F := LA.localCompletionFamily c t ht
    HasSmoothTargetFamilyOn (𝓡∂ 2) N F.base
      (fun s x => R s (chartValue c.val (O.compact s) s x)))
  (hflow : ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet),
    HasRealSmoothFlowGermsOn N (LA.localCompletionFamily c t ht).base
      (fun s r y => R s ((Z s).completeFlow.flow r ((R s).symm y))))

/-- The rank-one constructor produces the existing original bundle of a
finite ribbon, with the exact same prescribed ambient section. -/
def smoothSourceFlowZeroBundle : OriginalZeroBundle where
  A := A
  M := M
  EA := EA
  EM := EM
  PA := PA
  PW := PW
  PJ := PJ
  LA := LA
  hPJ := hPJ
  μ := μ
  S := O.originalMaslovData (n := 1) rfl (smoothSourceMaslovRepresentative Z N η f R hη)
  hS := (O.tensorGerms_of_smooth_source_flow (n := 1) rfl Z N η f R hη hi hflow).coframeGerms

/-- The full zero-ribbon realization retains its entire ribbon core,
actual grade and ambient/finite-ribbon marking recovery capabilities. -/
def smoothSourceFlowZeroRealization :
    OriginalZeroRealization (smoothSourceFlowZeroBundle PA PW PJ LA hPJ μ Z O N η f R hη hi hflow) :=
  (smoothSourceFlowZeroBundle PA PW PJ LA hPJ μ Z O N η f R hη hi hflow).realize


variable (hα : N.IsSmoothIntervalFormFamily
  (fun s => N.pullback (Z s).manifold (R s).symm (Z s).primitive))

/-- Ordinary smooth source primitives and compact inclusions produce the
rank-one original bundle, with its finite ribbon and prescribed section. -/
def smoothSourceZeroBundle : OriginalZeroBundle where
  A := A
  M := M
  EA := EA
  EM := EM
  PA := PA
  PW := PW
  PJ := PJ
  LA := LA
  hPJ := hPJ
  μ := μ
  S := O.originalMaslovData (n := 1) rfl (smoothSourceMaslovRepresentative Z N η f R hη)
  hS := (O.tensorGerms_of_smooth_source (n := 1) rfl Z N η f R hη hi hα).coframeGerms

/-- The full zero-ribbon realization retains its entire ribbon core,
actual grade and ambient/finite-ribbon marking recovery capabilities. -/
def smoothSourceZeroRealization :
    OriginalZeroRealization (smoothSourceZeroBundle PA PW PJ LA hPJ μ Z O N η f R hη hi hα) :=
  (smoothSourceZeroBundle PA PW PJ LA hPJ μ Z O N η f R hη hi hα).realize

end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
