import FsFltz.Geometry.OriginalBundleLocalMaslovSourceRegularity
import FsFltz.Geometry.OriginalBundleLocalSourceFlowGerms
import FsFltz.Geometry.OriginalBundleMaslovSectionPullback
import FsFltz.Geometry.OriginalBundleFiniteRealization

/-!
# Original realizations from source data on retained local presentations

Source: `geoemtric-part-fsf.tex`, smooth extensions (119–122), `def:chain`
(163–199), `def:maslov` (212–244), and `sec:lean` (788–814).
One prescribed representative on each actual completed source is transported
through each retained local presentation. The fixed smooth model may differ
between local bases and no presentation, symplectic law or source section is
required outside its retained base. Ordinary source primitive, inclusion and
section coefficient regularity produce the actual marking and tensor germs.
The existing original realization then carries the same prescribed data.

The correspondence from a smooth section on the retained collar-generated
completed total family to these ordinary local presentation inputs remains a
separate foundation. Neither a target chain nor an encoded grading is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

/-- Raw source complex fields in a retained local presentation. The zero
values outside that base are merely a totalization of coordinate values. -/
def localSourceAlmostComplex {n : ℕ}
    (Z : Parameter → CompleteLiouvilleManifold (2 * n))
    (N : SmoothManifold (2 * n)) (B : Set Parameter)
    (R : ∀ s, s ∈ B → (Z s).manifold.SmoothEquiv N)
    (σ : ∀ s, MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive))
    (r : ℝ) : AlmostComplexField N :=
  if hr : r ∈ parameterInterval then
    if hs : (⟨r, hr⟩ : Parameter) ∈ B then
      pullbackAlmostComplex N (Z ⟨r, hr⟩).manifold (R ⟨r, hr⟩ hs).symm (σ ⟨r, hr⟩).J
    else 0
  else 0

/-- The entire prescribed source tensor is transported in every slot through
that same local presentation, with no section prescribed off the base. -/
def localSourceSquaredTensor {n : ℕ}
    (Z : Parameter → CompleteLiouvilleManifold (2 * n))
    (N : SmoothManifold (2 * n)) (B : Set Parameter)
    (R : ∀ s, s ∈ B → (Z s).manifold.SmoothEquiv N)
    (σ : ∀ s, MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive))
    (r : ℝ) : N.Point → SquaredCanonicalTensor n :=
  if hr : r ∈ parameterInterval then
    if hs : (⟨r, hr⟩ : Parameter) ∈ B then
      pullbackSquaredTensor N (Z ⟨r, hr⟩).manifold (R ⟨r, hr⟩ hs).symm (σ ⟨r, hr⟩).tensor
    else 0
  else 0

@[simp] theorem localSourceAlmostComplex_apply {n : ℕ}
    (Z : Parameter → CompleteLiouvilleManifold (2 * n))
    (N : SmoothManifold (2 * n)) (B : Set Parameter)
    (R : ∀ s, s ∈ B → (Z s).manifold.SmoothEquiv N)
    (σ : ∀ s, MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive)) (s : Parameter) (hs : s ∈ B) :
    localSourceAlmostComplex Z N B R σ s.val =
      pullbackAlmostComplex N (Z s).manifold (R s hs).symm (σ s).J := by
  simp only [localSourceAlmostComplex, parameterInterval, s.property, ↓reduceDIte, hs]

@[simp] theorem localSourceSquaredTensor_apply {n : ℕ}
    (Z : Parameter → CompleteLiouvilleManifold (2 * n))
    (N : SmoothManifold (2 * n)) (B : Set Parameter)
    (R : ∀ s, s ∈ B → (Z s).manifold.SmoothEquiv N)
    (σ : ∀ s, MaslovRepresentative (Z s).manifold
      ((Z s).manifold.exteriorDerivative (Z s).primitive)) (s : Parameter) (hs : s ∈ B) :
    localSourceSquaredTensor Z N B R σ s.val =
      pullbackSquaredTensor N (Z s).manifold (R s hs).symm (σ s).tensor := by
  simp only [localSourceSquaredTensor, parameterInterval, s.property, ↓reduceDIte, hs]

section LocalSource

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P}
  {Z : Parameter → CompleteLiouvilleManifold (2 * n)}

namespace OriginalBundleCompletionMarkingData

variable (O : OriginalBundleCompletionMarkingData L Z) (hdim : k + 1 = 2 * n)
  (σ : ∀ s, MaslovRepresentative (Z s).manifold
    ((Z s).manifold.exteriorDerivative (Z s).primitive))

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The local source coordinates cancel without any assumed original-field
identity. The source representative is the one prescribed before realization. -/
theorem localSource_originalJ
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (N : SmoothManifold (2 * n))
    (R : ∀ s, s ∈ (L.localCompletionFamily c t ht).base → (Z s).manifold.SmoothEquiv N)
    (s : Parameter) (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (O.originalMaslovData hdim σ).J c t ht s hs =
      pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold N
        (CompletedMaslovDimension.comparison hdim
          ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient N
          ((O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s hs)))
        (localSourceAlmostComplex Z N (L.localCompletionFamily c t ht).base R σ s.val) := by
  rw [O.originalMaslovData_J, localSourceAlmostComplex_apply Z N _ R σ s hs,
    ← pullbackAlmostComplex_trans]
  rw [CompletedMaslovDimension.comparison_trans]
  have heq : ((O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s hs)).trans
      (R s hs).symm = O.localEquiv (L.localCompletionFamily c t ht) s hs := by
    apply Diffeomorph.ext
    intro x
    exact (R s hs).symm_apply_apply _
  rw [heq]
  rfl

omit [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Local source coordinates also cancel in every slot of the same prescribed
full tensor. No desired original tensor identity is supplied as a premise. -/
theorem localSource_originalTensor
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (N : SmoothManifold (2 * n))
    (R : ∀ s, s ∈ (L.localCompletionFamily c t ht).base → (Z s).manifold.SmoothEquiv N)
    (s : Parameter) (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    (O.originalMaslovData hdim σ).tensor c t ht s hs =
      pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold N
        (CompletedMaslovDimension.comparison hdim
          ((L.localCompletionFamily c t ht).sliceCompletion L s).ambient N
          ((O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s hs)))
        (localSourceSquaredTensor Z N (L.localCompletionFamily c t ht).base R σ s.val) := by
  rw [O.originalMaslovData_tensor, localSourceSquaredTensor_apply Z N _ R σ s hs,
    ← pullbackSquaredTensor_trans]
  rw [CompletedMaslovDimension.comparison_trans]
  have heq : ((O.localEquiv (L.localCompletionFamily c t ht) s hs).trans (R s hs)).trans
      (R s hs).symm = O.localEquiv (L.localCompletionFamily c t ht) s hs := by
    apply Diffeomorph.ext
    intro x
    exact (R s hs).symm_apply_apply _
  rw [heq]
  rfl

end OriginalBundleCompletionMarkingData

/-- A local source presentation carries ordinary source primitive and compact
inclusion smoothness only on its retained base. Its completed model is allowed
to differ from the model of another retained base. -/
structure OriginalLocalCompletedSourcePresentation
    (O : OriginalBundleCompletionMarkingData L Z)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) where
  manifold : SmoothManifold (2 * n)
  equiv : ∀ s, s ∈ (L.localCompletionFamily c t ht).base →
    (Z s).manifold.SmoothEquiv manifold
  primitive_smooth : IsSmoothSourcePrimitiveOnBase Z manifold
    (L.localCompletionFamily c t ht).base equiv
  inclusion_smooth : HasSmoothTargetFamilyOnBase (𝓡∂ (k + 1)) manifold
    (L.localCompletionFamily c t ht).base
    (fun s hs x => equiv s hs (chartValue c.val (O.compact s) s x))

namespace OriginalBundleCompletionMarkingData

variable (O : OriginalBundleCompletionMarkingData L Z) (hdim : k + 1 = 2 * n)
  (σ : ∀ s, MaslovRepresentative (Z s).manifold
    ((Z s).manifold.exteriorDerivative (Z s).primitive))
  (A : ∀ (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet), OriginalLocalCompletedSourcePresentation O c t ht)
  (hsection : ∀ c t ht, HasSmoothMaslovCoefficientGermsOn (A c t ht).manifold
    (L.localCompletionFamily c t ht).base
    (localSourceAlmostComplex Z (A c t ht).manifold (L.localCompletionFamily c t ht).base
      (A c t ht).equiv σ)
    (localSourceSquaredTensor Z (A c t ht).manifold (L.localCompletionFamily c t ht).base
      (A c t ht).equiv σ))

include hsection in
/-- Ordinary local source data produce all original tensor germs. The actual
field and full-tensor identities, finite-flow regularity and actual marking
regularity are derived; no original tensor/coframe/marking germ is supplied. -/
theorem tensorGerms_of_local_smooth_source :
    OriginalLocalCompletionMaslovTensorGerms (O.originalMaslovData hdim σ) := by
  apply OriginalLocalCompletionMaslovData.tensorGerms_of_localSource_markingMapGerms
    (O.originalMaslovData hdim σ) (fun c t ht => (A c t ht).manifold)
    (fun c t ht => localSourceAlmostComplex Z (A c t ht).manifold
      (L.localCompletionFamily c t ht).base (A c t ht).equiv σ)
    (fun c t ht => localSourceSquaredTensor Z (A c t ht).manifold
      (L.localCompletionFamily c t ht).base (A c t ht).equiv σ) hsection
    (fun c t ht s hs => (O.localEquiv (L.localCompletionFamily c t ht) s hs).trans
      ((A c t ht).equiv s hs))
  · intro c t ht s hs
    exact O.localSource_originalJ hdim σ c t ht (A c t ht).manifold (A c t ht).equiv s hs
  · intro c t ht s hs
    exact O.localSource_originalTensor hdim σ c t ht (A c t ht).manifold (A c t ht).equiv s hs
  · intro c t ht
    exact (O.localEquiv_realGerms_of_source_inclusion_and_primitive_smooth_onBase
      (L.localCompletionFamily c t ht) (A c t ht).manifold (A c t ht).equiv
      (A c t ht).inclusion_smooth (A c t ht).primitive_smooth).1
  · intro c t ht
    exact (O.localEquiv_realGerms_of_source_inclusion_and_primitive_smooth_onBase
      (L.localCompletionFamily c t ht) (A c t ht).manifold (A c t ht).equiv
      (A c t ht).inclusion_smooth (A c t ht).primitive_smooth).2

end OriginalBundleCompletionMarkingData
end LocalSource

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
  (σ : ∀ s, MaslovRepresentative (Z s).manifold
    ((Z s).manifold.exteriorDerivative (Z s).primitive))
  (V : ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet), OriginalLocalCompletedSourcePresentation O c t ht)
  (hsection : ∀ c t ht, HasSmoothMaslovCoefficientGermsOn (V c t ht).manifold
    (LA.localCompletionFamily c t ht).base
    (localSourceAlmostComplex Z (V c t ht).manifold (LA.localCompletionFamily c t ht).base
      (V c t ht).equiv σ)
    (localSourceSquaredTensor Z (V c t ht).manifold (LA.localCompletionFamily c t ht).base
      (V c t ht).equiv σ))

/-- The existing positive-ribbon realization consumes source regularity only
on each retained local base, keeping the original pair geometry and the same
prescribed source fields and full section. -/
def localSmoothSourcePositiveBundle : OriginalPositiveBundle a k n where
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
  S := O.originalMaslovData hdimA σ
  hS := (O.tensorGerms_of_local_smooth_source hdimA σ V hsection).coframeGerms

/-- Full realization retains the actual deformation, its prescribed grading
and both original marking-recovery capabilities. -/
def localSmoothSourcePositiveRealization :
    OriginalPositiveRealization
      (localSmoothSourcePositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O σ V hsection) :=
  (localSmoothSourcePositiveBundle hdimA hdimM PA PM PW PJ LA LM LP Z O σ V hsection).realize

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
  (Z : Parameter → CompleteLiouvilleManifold (2 * 1))
  (O : OriginalBundleCompletionMarkingData LA Z)
  (σ : ∀ s, MaslovRepresentative (Z s).manifold
    ((Z s).manifold.exteriorDerivative (Z s).primitive))
  (V : ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
    (t : Parameter) (ht : t ∈ c.val.baseSet), OriginalLocalCompletedSourcePresentation (n := 1) O c t ht)
  (hsection : ∀ c t ht, HasSmoothMaslovCoefficientGermsOn (n := 1) (V c t ht).manifold
    (LA.localCompletionFamily c t ht).base
    (localSourceAlmostComplex (n := 1) Z (V c t ht).manifold (LA.localCompletionFamily c t ht).base
      (V c t ht).equiv σ)
    (localSourceSquaredTensor (n := 1) Z (V c t ht).manifold (LA.localCompletionFamily c t ht).base
      (V c t ht).equiv σ))

/-- Rank one uses the finite zero-dimensional ribbon and the same prescribed
source section, with local source presentations only on retained bases. -/
def localSmoothSourceZeroBundle : OriginalZeroBundle where
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
  S := O.originalMaslovData (n := 1) rfl σ
  hS := (O.tensorGerms_of_local_smooth_source (n := 1) rfl σ V hsection).coframeGerms

/-- Full zero-ribbon realization retains the entire ribbon core, grade and
ambient/finite-ribbon original marking recovery. -/
def localSmoothSourceZeroRealization :
    OriginalZeroRealization (localSmoothSourceZeroBundle PA PW PJ LA hPJ μ Z O σ V hsection) :=
  (localSmoothSourceZeroBundle PA PW PJ LA hPJ μ Z O σ V hsection).realize

end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
