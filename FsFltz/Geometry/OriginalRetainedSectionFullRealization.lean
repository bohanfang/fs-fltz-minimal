import FsFltz.Geometry.OriginalRetainedBundleMaslovRealization

/-!
# Full original realizations from arbitrary retained canonical-square sections

Source: `geoemtric-part-fsf.tex`, smooth-extension convention, lines 119–122;
`def:chain`, lines 163–199; `def:maslov`, lines 212–244;
`g:initial`, lines 374–384; and `sec:lean`, lines 788–814.
The compatible complex data are given on the retained collar-generated
completed family. An arbitrary nowhere-zero section of its actual canonical
square bundle, with its defining ordinary smooth map and overlap laws,
produces the original Maslov data and its coframe regularity. The existing
full positive- and zero-ribbon realization constructors then retain exact
field and full-tensor recovery, the same ambient grade, and both ambient
and ribbon marking capabilities. No original encoded Maslov data, coframe
germs, represented deformation or grading are input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Bundle
open FsFltz.Geometry.IntrinsicLiouville
open FsFltz.Geometry.IntrinsicZeroLiouville
open FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.IntrinsicSmoothBundle

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
  (D : OriginalRetainedMaslovComplexData PA LA hdimA)
  (hD : OriginalRetainedMaslovComplexRegularity D)
  (σ : OriginalRetainedMaslovSection D)

/-- The arbitrary actual canonical-square section supplies both original
Maslov data and their coframe regularity. The original geometry is retained. -/
def retainedSectionPositiveBundle : OriginalPositiveBundle a k n where
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
  S := σ.toOriginalMaslovData
  hS := σ.coframeGerms hD

/-- The full positive-ribbon realization carries the same arbitrary source
section, exact fields and tensors, its ambient grading and both markings. -/
def retainedSectionPositiveRealization :
    OriginalPositiveRealization
      (retainedSectionPositiveBundle hdimA hdimM PA PM PW PJ LA LM LP D hD σ) :=
  (retainedSectionPositiveBundle hdimA hdimM PA PM PW PJ LA LM LP D hD σ).realize

/-- The chosen full realization recovers the prescribed compatible field
and every slot of the tensor produced by the actual retained section. -/
theorem retainedSectionPositiveRealization_recovery :
    let R := retainedSectionPositiveRealization hdimA hdimM PA PM PW PJ LA LM LP D hD σ
    ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
      (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
      (hs : s ∈ (LA.localCompletionFamily c t ht).base),
      pullbackAlmostComplex (localMaslovAmbient hdimA LA c t ht s).manifold
        R.Q.source.ambientManifold
        (localMaslovComparison R.cA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs)
        (R.f.J s.val) = D.J c t ht s hs ∧
      pullbackSquaredTensor (localMaslovAmbient hdimA LA c t ht s).manifold
        R.Q.source.ambientManifold
        (localMaslovComparison R.cA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs)
        (R.f.tensor s.val) = originalRetainedMaslovTensor D σ.sectionValue c t ht s hs := by
  intro R c t ht s hs
  exact R.recovery c t ht s hs

/-- Endpoint representatives of that same realization recover the actual
retained field and section tensor, without a new endpoint grading input. -/
theorem retainedSectionPositiveRealization_endpointRecovery :
    let R := retainedSectionPositiveRealization hdimA hdimM PA PM PW PJ LA LM LP D hD σ
    ∀ (c : OriginalCompactChart (k := a) (M := A) (E := EA))
      (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
      (hs : s ∈ (LA.localCompletionFamily c t ht).base),
      pullbackAlmostComplex (localMaslovAmbient hdimA LA c t ht s).manifold
        (R.Q.pair s).ambientManifold
        ((localMaslovComparison R.cA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs).trans
          (R.Q.ambientCompletionPresentation s).equiv)
        ((R.Q.maslovFamilyRepresentative R.f) s).J = D.J c t ht s hs ∧
      pullbackSquaredTensor (localMaslovAmbient hdimA LA c t ht s).manifold
        (R.Q.pair s).ambientManifold
        ((localMaslovComparison R.cA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs).trans
          (R.Q.ambientCompletionPresentation s).equiv)
        ((R.Q.maslovFamilyRepresentative R.f) s).tensor =
          originalRetainedMaslovTensor D σ.sectionValue c t ht s hs := by
  intro R c t ht s hs
  exact R.endpointRecovery c t ht s hs

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
  (D : OriginalRetainedMaslovComplexData PA LA (n := 1) rfl)
  (hD : OriginalRetainedMaslovComplexRegularity D)
  (σ : OriginalRetainedMaslovSection D)

/-- The actual arbitrary source section also supplies the rank-one full
bundle, with its finite zero-dimensional ribbon and unchanged intrinsic core. -/
def retainedSectionZeroBundle : OriginalZeroBundle where
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
  S := σ.toOriginalMaslovData
  hS := σ.coframeGerms hD

/-- Full zero-ribbon realization retains the same arbitrary source section,
the entire finite ribbon core, grading and both marking recoveries. -/
def retainedSectionZeroRealization :
    OriginalZeroRealization (retainedSectionZeroBundle PA PW PJ LA hPJ μ D hD σ) :=
  (retainedSectionZeroBundle PA PW PJ LA hPJ μ D hD σ).realize

/-- The rank-one realization recovers the prescribed field and the full
tensor of the arbitrary retained canonical-square section. -/
theorem retainedSectionZeroRealization_recovery :
    let R := retainedSectionZeroRealization PA PW PJ LA hPJ μ D hD σ
    ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
      (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
      (hs : s ∈ (LA.localCompletionFamily c t ht).base),
      pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
        R.Q.source.ambientManifold
        (localMaslovComparison R.eA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs)
        (R.f.J s.val) = D.J c t ht s hs ∧
      pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
        R.Q.source.ambientManifold
        (localMaslovComparison R.eA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs)
        (R.f.tensor s.val) = originalRetainedMaslovTensor D σ.sectionValue c t ht s hs := by
  intro R c t ht s hs
  exact R.recovery c t ht s hs

/-- The same zero-ribbon endpoint representatives recover that field and
section tensor under the actual original completion comparisons. -/
theorem retainedSectionZeroRealization_endpointRecovery :
    let R := retainedSectionZeroRealization PA PW PJ LA hPJ μ D hD σ
    ∀ (c : OriginalCompactChart (k := 1) (M := A) (E := EA))
      (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
      (hs : s ∈ (LA.localCompletionFamily c t ht).base),
      pullbackAlmostComplex (localMaslovAmbient rfl LA c t ht s).manifold
        (R.Q.pair s).ambientManifold
        ((localMaslovComparison R.eA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs).trans
          (R.Q.ambientCompletionPresentation s).equiv)
        ((R.Q.maslovFamilyRepresentative R.f) s).J = D.J c t ht s hs ∧
      pullbackSquaredTensor (localMaslovAmbient rfl LA c t ht s).manifold
        (R.Q.pair s).ambientManifold
        ((localMaslovComparison R.eA R.heA R.hbaseA R.Q R.eAs R.hp R.hc c t ht s hs).trans
          (R.Q.ambientCompletionPresentation s).equiv)
        ((R.Q.maslovFamilyRepresentative R.f) s).tensor =
          originalRetainedMaslovTensor D σ.sectionValue c t ht s hs := by
  intro R c t ht s hs
  exact R.endpointRecovery c t ht s hs

end ZeroRibbon

end FsFltz.Geometry.IntrinsicSmoothBundle
