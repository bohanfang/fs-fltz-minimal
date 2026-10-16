import FsFltz.Geometry.IntrinsicBundleLocalCompletionMaslovSmoothDescent
import FsFltz.Geometry.IntrinsicNativeCompletionOriginalSectionEndpoints

/-!
# A Maslov family from the preselected original completed data

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. Original coframe and scalar germs descend through
the constructed comparisons and produce a family on the very same retained
pair deformation. Every original full tensor and complex field is retained,
including the two parameter endpoints.

The original data and their source extension convention remain conditional
inputs. This foundation does not construct the geometric comparison chain
or identify its prescribed endpoint grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Bundle
open FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.IntrinsicSmoothBundle

private theorem canonicalSquareMap_cast {n : ℕ}
    {J K : Model (2 * n) →L[ℝ] Model (2 * n)} (h : J = K)
    (s : CanonicalTensorSquare K) :
    (canonicalSquareMap J (cast (congrArg CanonicalTensorSquare h.symm) s)).val =
      (canonicalSquareMap K s).val := by
  cases h
  rfl

private theorem canonicalTensorSquare_cast_ne_zero {n : ℕ}
    {J K : Model (2 * n) →L[ℝ] Model (2 * n)} (h : J = K)
    (s : CanonicalTensorSquare K) (hs : s ≠ 0) :
    cast (congrArg CanonicalTensorSquare h.symm) s ≠ 0 := by
  cases h
  exact hs

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {E : Parameter → Type*} [∀ s, TopologicalSpace (E s)]
  [TopologicalSpace (Bundle.TotalSpace M E)]
  [SmoothCompactBundle (𝓡∂ (k + 1)) (F := M) E]
  {P : BundlePrimitiveData (k := k) (M := M) E}
  {L : OriginalBundleLiouvilleLaws P} {hdim : k + 1 = 2 * n}

namespace OriginalLocalCompletionMaslovData

variable (S : OriginalLocalCompletionMaslovData P L hdim)
  (g : Trivialization M (π M E)) (hg : CompatibleTrivialization (𝓡∂ (k + 1)) E g)
  (hbase : g.baseSet = univ) (Q : PairDeformation n)
  (eAs : ∀ s, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
    (Q.pair s).ambientDomain.domain.Point ∞)
  (hp : ∀ s x, ((Q.pair s).ambientDomain.liouville.primitive (eAs s x).val).compContinuousLinearMap
    (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (eAs s y).val) x) =
      P.formInTrivialization g s x)
  (hc : ∀ s, HasNativeCoordinateExtensions (k := k)
    (Q.pair s).ambientDomain.domain.extension (fun x => (eAs s x).val))

/-- A raw real-indexed field with exactly the prescribed descended
interval values. Smoothness is subsequently supplied by local extensions. -/
def descendedJExtension (t : ℝ) : AlmostComplexField Q.source.ambientManifold :=
  if ht : t ∈ parameterInterval then S.descendedJ g hg hbase Q eAs hp hc ⟨t, ht⟩ else 0

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
@[simp] theorem descendedJExtension_apply (s : Parameter) :
    S.descendedJExtension g hg hbase Q eAs hp hc s.val =
      S.descendedJ g hg hbase Q eAs hp hc s := by
  unfold descendedJExtension
  split
  · rfl
  · rename_i h
    exact (h s.property).elim

/-- The actual descended tensor-product section, transported only by
the equality of its prescribed interval complex structures. -/
def descendedIntervalTensorSection (p : Parameter × Q.source.ambientManifold.Point) :
    CanonicalTensorSquare (S.descendedJExtension g hg hbase Q eAs hp hc p.1.val p.2) :=
  cast (congrArg CanonicalTensorSquare
    (congrArg (fun J => J p.2) (S.descendedJExtension_apply g hg hbase Q eAs hp hc p.1)).symm)
      (S.descendedTensorSquareSection g hg hbase Q eAs hp hc p.1 p.2)

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem canonicalSquareMap_descendedIntervalTensorSection
    (p : Parameter × Q.source.ambientManifold.Point) :
    (canonicalSquareMap (S.descendedJExtension g hg hbase Q eAs hp hc p.1.val p.2)
      (S.descendedIntervalTensorSection g hg hbase Q eAs hp hc p)).val =
        S.descendedTensor g hg hbase Q eAs hp hc p.1 p.2 := by
  exact (canonicalSquareMap_cast (n := n)
    (J := S.descendedJExtension g hg hbase Q eAs hp hc p.1.val p.2)
    (K := S.descendedJ g hg hbase Q eAs hp hc p.1 p.2)
    (congrArg (fun J => J p.2) (S.descendedJExtension_apply g hg hbase Q eAs hp hc p.1))
    (S.descendedTensorSquareSection g hg hbase Q eAs hp hc p.1 p.2)).trans (congrArg Subtype.val
      (S.canonicalSquareMap_descendedTensorSquareSection g hg hbase Q eAs hp hc p.1 p.2))

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
theorem descendedIntervalTensorSection_ne_zero
    (p : Parameter × Q.source.ambientManifold.Point) :
    S.descendedIntervalTensorSection g hg hbase Q eAs hp hc p ≠ 0 := by
  exact canonicalTensorSquare_cast_ne_zero (n := n)
    (J := S.descendedJExtension g hg hbase Q eAs hp hc p.1.val p.2)
    (K := S.descendedJ g hg hbase Q eAs hp hc p.1 p.2)
    (congrArg (fun J => J p.2) (S.descendedJExtension_apply g hg hbase Q eAs hp hc p.1))
    (S.descendedTensorSquareSection g hg hbase Q eAs hp hc p.1 p.2)
    (S.descendedTensorSquareSection_ne_zero g hg hbase Q eAs hp hc p.1 p.2)

variable (hS : OriginalLocalCompletionMaslovCoframeGerms S)
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
/-- The original coframe germs give genuine local endomorphism extensions
of the literal descended field at every interval point. -/
theorem localSmoothComplexExtensions_descended :
    HasLocalSmoothIntervalComplexExtensions Q.source.ambientManifold
      (S.descendedJExtension g hg hbase Q eAs hp hc) := by
  intro p
  obtain ⟨U, hU, hpU, B, _, _, a, _, hJ, _, hmatch⟩ :=
    S.exists_local_descendedMaslovExtension g hg hbase Q eAs hp hc hS
      eBs hb hsquareB R hR hsquareA p.1 p.2
  refine ⟨U, hU, hpU, fun z => coframeComplexStructure (B z), hJ, ?_⟩
  intro z hz
  rw [S.descendedJExtension_apply]
  exact (hmatch z.1 z.2 hz).1

include hS eBs hb hsquareB R hR hsquareA in
/-- The same transported coframe and scalar extend the coefficient of the
actual descended tensor-product section, with no change to its full tensor. -/
theorem localSmoothTensorCoefficients_descended :
    HasLocalSmoothIntervalTensorCoefficients Q.source.ambientManifold
      (S.descendedJExtension g hg hbase Q eAs hp hc)
      (S.descendedIntervalTensorSection g hg hbase Q eAs hp hc) := by
  intro p
  obtain ⟨U, hU, hpU, B, hB, hBi, a, ha, _, _, hmatch⟩ :=
    S.exists_local_descendedMaslovExtension g hg hbase Q eAs hp hc hS
      eBs hb hsquareB R hR hsquareA p.1 p.2
  let c : IntervalCanonicalChart Q.source.ambientManifold
      (S.descendedJExtension g hg hbase Q eAs hp hc) :=
    { domain := U
      isOpen_domain := hU
      coframe := B
      smooth_coframe := hB
      invertible_coframe := hBi
      intertwines_coframe := by
        intro z hz ht v
        have hm := (hmatch ⟨z.1, ht⟩ z.2 hz).1
        rw [S.descendedJExtension_apply g hg hbase Q eAs hp hc ⟨z.1, ht⟩, ← hm]
        exact coframeComplexStructure_intertwines (B z) (hBi z hz) v }
  refine ⟨c, U, hU, Subset.refl _, hpU, a, ha, ?_⟩
  intro z hz
  rw [← c.coefficient_squareMap,
    S.canonicalSquareMap_descendedIntervalTensorSection g hg hbase Q eAs hp hc z,
    ← (hmatch z.1 z.2 hz).2]
  change a (z.1.val, z.2) = squaredCoframeCoefficient (B (z.1.val, z.2))
    (a (z.1.val, z.2) • coframeSquaredGenerator (B (z.1.val, z.2)))
  simp only [squaredCoframeCoefficient, smul_apply, smul_eq_mul]
  rw [coframeSquaredGenerator_frame (B (z.1.val, z.2)) (hBi _ hz), mul_one]

include hS eBs hb hsquareB R hR hsquareA in
/-- Source-only original regularity and the constructed comparisons give
one Maslov family on this very completed deformation. Every prescribed
interval complex field and full tensor, including zero and one, is fixed. -/
theorem exists_maslovFamily_descended :
    ∃ f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension,
      (∀ s : Parameter, f.J s.val = S.descendedJ g hg hbase Q eAs hp hc s) ∧
      ∀ s : Parameter, f.tensor s.val = S.descendedTensor g hg hbase Q eAs hp hc s := by
  have hcompatible : ∀ t ∈ parameterInterval,
      IsCompatibleAlmostComplex Q.source.ambientManifold (Q.completedSymplecticExtension t)
        (S.descendedJExtension g hg hbase Q eAs hp hc t) := by
    intro t ht
    rw [S.descendedJExtension_apply g hg hbase Q eAs hp hc ⟨t, ht⟩,
      Q.completedSymplecticExtension_apply ⟨t, ht⟩]
    exact S.descendedJ_compatible g hg hbase Q eAs hp hc ⟨t, ht⟩
  obtain ⟨f, hfJ, hfT⟩ := exists_maslovFamily_of_localExtensions
    (S.descendedJExtension g hg hbase Q eAs hp hc) hcompatible
    (S.localSmoothComplexExtensions_descended g hg hbase Q eAs hp hc hS
      eBs hb hsquareB R hR hsquareA)
    (S.descendedIntervalTensorSection g hg hbase Q eAs hp hc)
    (S.descendedIntervalTensorSection_ne_zero g hg hbase Q eAs hp hc)
    (S.localSmoothTensorCoefficients_descended g hg hbase Q eAs hp hc hS
      eBs hb hsquareB R hR hsquareA)
  refine ⟨f, ?_, ?_⟩
  · intro s
    exact (hfJ s).trans (S.descendedJExtension_apply g hg hbase Q eAs hp hc s)
  · intro s
    funext x
    exact (hfT (s, x)).trans
      (S.canonicalSquareMap_descendedIntervalTensorSection g hg hbase Q eAs hp hc (s, x))

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Any family with the prescribed descended values recovers the original
complex field and complete two-block tensor in every retained local chart. -/
theorem pullback_maslovFamily_descended
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (hfJ : ∀ s : Parameter, f.J s.val = S.descendedJ g hg hbase Q eAs hp hc s)
    (hfT : ∀ s : Parameter, f.tensor s.val = S.descendedTensor g hg hbase Q eAs hp hc s)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet) (s : Parameter)
    (hs : s ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht s).manifold
      Q.source.ambientManifold (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
      (f.J s.val) = S.J c t ht s hs ∧
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht s).manifold
      Q.source.ambientManifold (localMaslovComparison g hg hbase Q eAs hp hc c t ht s hs)
      (f.tensor s.val) = S.tensor c t ht s hs := by
  rw [hfJ s, hfT s]
  exact ⟨S.pullback_descendedJ g hg hbase Q eAs hp hc c t ht s hs,
    S.pullback_descendedTensor g hg hbase Q eAs hp hc c t ht s hs⟩

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Initial endpoint recovery uses every original chart retaining zero,
through the same comparisons used on the whole interval. -/
theorem pullback_maslovFamily_descended_zero
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (hfJ : ∀ s : Parameter, f.J s.val = S.descendedJ g hg hbase Q eAs hp hc s)
    (hfT : ∀ s : Parameter, f.tensor s.val = S.descendedTensor g hg hbase Q eAs hp hc s)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (hs : parameterZero ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht parameterZero).manifold
      Q.source.ambientManifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterZero hs)
      (f.J 0) = S.J c t ht parameterZero hs ∧
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht parameterZero).manifold
      Q.source.ambientManifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterZero hs)
      (f.tensor 0) = S.tensor c t ht parameterZero hs :=
  S.pullback_maslovFamily_descended g hg hbase Q eAs hp hc f hfJ hfT
    c t ht parameterZero hs

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Terminal endpoint recovery preserves the original field and every
tensor slot, with no interval-interior restriction. -/
theorem pullback_maslovFamily_descended_one
    (f : MaslovFamily Q.source.ambientManifold Q.completedSymplecticExtension)
    (hfJ : ∀ s : Parameter, f.J s.val = S.descendedJ g hg hbase Q eAs hp hc s)
    (hfT : ∀ s : Parameter, f.tensor s.val = S.descendedTensor g hg hbase Q eAs hp hc s)
    (c : OriginalCompactChart (k := k) (M := M) (E := E))
    (t : Parameter) (ht : t ∈ c.val.baseSet)
    (hs : parameterOne ∈ (L.localCompletionFamily c t ht).base) :
    pullbackAlmostComplex (localMaslovAmbient hdim L c t ht parameterOne).manifold
      Q.source.ambientManifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterOne hs)
      (f.J 1) = S.J c t ht parameterOne hs ∧
    pullbackSquaredTensor (localMaslovAmbient hdim L c t ht parameterOne).manifold
      Q.source.ambientManifold
      (localMaslovComparison g hg hbase Q eAs hp hc c t ht parameterOne hs)
      (f.tensor 1) = S.tensor c t ht parameterOne hs :=
  S.pullback_maslovFamily_descended g hg hbase Q eAs hp hc f hfJ hfT
    c t ht parameterOne hs

end OriginalLocalCompletionMaslovData

end FsFltz.Geometry.IntrinsicSmoothBundle
