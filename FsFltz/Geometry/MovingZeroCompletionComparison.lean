import FsFltz.Geometry.MovingCompletionComparison
import FsFltz.Geometry.IntrinsicNativeFamilyEndpointComparison

/-!
# Strict comparisons with prescribed moving zero-dimensional completions

Source: `geoemtric-part-fsf.tex`, zero-dimensional conventions, lines
127–128 and `def:pair`, lines 159–160; `def:chain`, lines 163–189;
`sec:lean`, lines 788–793, 805–814 and 825–830.

The actual native compact inclusions are diffeomorphisms onto the completed
ambients in dimension zero. The independently prescribed moving compact
and completed presentations cancel through their own compact squares. The
remaining relative map and its inverse are conjugates of the constructed
jointly smooth native family. Thus the completion comparison requires no
joint comparison hypothesis, collar compatibility, reference normalization
or nonemptiness. The original varying primitives are retained by pullback.

This is a rank-one ribbon foundation, not a geometric comparison chain or
a full-fiber marking for the target theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.LocalizedCompletionFamily
open IntrinsicZeroLiouville SmoothManifold

private theorem intervalMaps_of_native_conjugation
    {M : Type} [TopologicalSpace M] [ChartedSpace (Model 0) M]
    (N N' : SmoothManifold 0)
    (a : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N.Point ∞)
    (b : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M N'.Point ∞)
    (T : ℝ → Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M M ∞)
    (hT : IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) T)
    (f : Parameter → N.Point → N'.Point)
    (heq : ∀ t x, f t (a x) = b ((T t.val).symm x))
    (fi : Parameter → N'.Point → N.Point)
    (hieq : ∀ t x, fi t (b x) = a (T t.val x)) :
    N.IsSmoothIntervalMapFamily N' f ∧ N'.IsSmoothIntervalMapFamily N fi := by
  constructor
  · let g : ℝ → N.Point → N'.Point := fun s z => b ((T s).symm (a.symm z))
    have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
        (fun z : ℝ × N.Point => g z.1 z.2) :=
      b.contMDiff.comp (hT.2.comp
        (contMDiff_fst.prodMk (a.symm.contMDiff.comp contMDiff_snd)))
    refine ⟨g, ⟨univ, isOpen_univ, subset_univ _, hg.contMDiffOn⟩, ?_⟩
    intro t
    funext z
    obtain ⟨x, rfl⟩ := a.surjective z
    change b ((T t.val).symm (a.symm (a x))) = _
    rw [a.symm_apply_apply]
    exact (heq t x).symm
  · let g : ℝ → N'.Point → N.Point := fun s z => a (T s (b.symm z))
    have hg : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model 0)) 𝓘(ℝ, Model 0) ∞
        (fun z : ℝ × N'.Point => g z.1 z.2) :=
      a.contMDiff.comp (hT.1.comp
        (contMDiff_fst.prodMk (b.symm.contMDiff.comp contMDiff_snd)))
    refine ⟨g, ⟨univ, isOpen_univ, subset_univ _, hg.contMDiffOn⟩, ?_⟩
    intro t
    funext z
    obtain ⟨x, rfl⟩ := b.surjective z
    change a (T t.val (b.symm (b x))) = _
    rw [b.symm_apply_apply]
    exact (hieq t x).symm

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {D : CompactDomain 0} {L : Parameter → LiouvilleStructure D}
local instance : ChartedSpace (Model 0) D.Point := D.zeroChartedSpace

omit [T2Space M] [SecondCountableTopology M] [IsManifold 𝓘(ℝ, Model 0) ∞ M] in
/-- The prescribed completed presentations cancel on every native point.
The formula uses the constructed compact transport itself, and includes
arbitrary prescribed presentation maps at the reference parameter. -/
theorem zeroReferenceComparison_native_formula
    (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.Point ∞)
    (R : LiouvilleDomain 0) (C : Completion R)
    (eR : letI := R.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M R.domain.Point ∞)
    (E : Parameter → LiouvilleDomain 0) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t))
    (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv
      (K t).ambient.manifold)
    (hs : ∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
        ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val) =
      (K t).inclusion.map ((h t).extensionEquiv (eR x).val))
    (t : Parameter) (x : M) :
    F.referenceComparison C E K h p q t
      ((F.collars parameterZero).cylindricalCompletion.inclusion.map
        ((e.trans (F.collars parameterZero).originalPointDiffeomorph_of_dimension_zero.symm) x).val) =
      C.inclusion.map
        (eR ((F.zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) e t.val).symm x)).val := by
  let u := (F.zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) e t.val).symm x
  have hH := F.zeroTransportedNativeDiffeomorph_square 𝓘(ℝ, Model 0) e t u
  have hu : F.zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) e t.val u = x :=
    (F.zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) e t.val).apply_symm_apply x
  rw [hu] at hH
  change (p t).equiv.symm (q t ((F.completionPresentation t).equiv
    ((e.trans (F.collars parameterZero).originalPointDiffeomorph_of_dimension_zero.symm) x).val)) = _
  rw [F.completionPresentation_eq]
  change (p t).equiv.symm (q t ((F.compactPresentation t).extensionEquiv
    ((e.trans (F.collars parameterZero).originalPointDiffeomorph_of_dimension_zero.symm) x).val)) = _
  rw [hH]
  change (p t).equiv.symm (q t ((F.collars t).cylindricalCompletion.inclusion.map
    ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) u).val)) = _
  rw [hs, ← (p t).compact_square (eR u).val (eR u).property]
  exact (p t).equiv.symm_apply_apply _

/-- Native compact regularity proves both directions of the actual relative
comparison jointly smooth across the interval endpoints. In dimension zero
the compact formula determines every completed point, including for an empty
source. No regularity of the supplied moving presentation maps is assumed. -/
theorem zeroReferenceComparison_smooth_of_native_square
    (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.Point ∞)
    (R : LiouvilleDomain 0) (C : Completion R)
    (eR : letI := R.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M R.domain.Point ∞)
    (E : Parameter → LiouvilleDomain 0) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t))
    (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv
      (K t).ambient.manifold)
    (hs : ∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
        ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val) =
      (K t).inclusion.map ((h t).extensionEquiv (eR x).val)) :
    (F.collars parameterZero).cylindricalCompletion.ambient.manifold.IsSmoothIntervalMapFamily
      C.ambient.manifold (fun t => F.referenceComparison C E K h p q t) ∧
    C.ambient.manifold.IsSmoothIntervalMapFamily
      (F.collars parameterZero).cylindricalCompletion.ambient.manifold
      (fun t => (F.referenceComparison C E K h p q t).symm) := by
  let a := endpointCompletionDiffeomorph (F.collars parameterZero).localizedDomain
    (F.collars parameterZero).cylindricalCompletion
    (e.trans (F.collars parameterZero).originalPointDiffeomorph_of_dimension_zero.symm)
  let b := endpointCompletionDiffeomorph R C eR
  let T := F.zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) e
  have hT : IsJointlySmoothDiffeomorphFamily 𝓘(ℝ, Model 0) T :=
    F.jointlySmooth_zeroTransportedNativeDiffeomorph 𝓘(ℝ, Model 0) e
  have heq (t : Parameter) (x : M) :
      F.referenceComparison C E K h p q t (a x) = b ((T t.val).symm x) :=
    F.zeroReferenceComparison_native_formula e R C eR E K h p q hs t x
  have hieq (t : Parameter) (x : M) :
      (F.referenceComparison C E K h p q t).symm (b x) = a (T t.val x) := by
    have hh := heq t (T t.val x)
    rw [(T t.val).symm_apply_apply] at hh
    exact (congrArg (F.referenceComparison C E K h p q t).symm hh).symm.trans
      ((F.referenceComparison C E K h p q t).symm_apply_apply _)
  exact intervalMaps_of_native_conjugation
    (F.collars parameterZero).cylindricalCompletion.ambient.manifold C.ambient.manifold
    a b T hT (fun t => F.referenceComparison C E K h p q t) heq
    (fun t => (F.referenceComparison C E K h p q t).symm) hieq

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.LocalizedCompletionFamily
open IntrinsicZeroLiouville SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]
  {D : CompactDomain 0} {L : Parameter → LiouvilleStructure D}
local instance : ChartedSpace (Model 0) D.Point := D.zeroChartedSpace

/-- Original native carrier diffeomorphisms construct the strict slice
comparisons on the independently prescribed moving completions. The two
compact formulas retain the same native points; neither joint comparison
regularity nor a primitive equality is supplied. -/
theorem exists_strictMovingZeroSliceComparisons
    (F : LocalizedCompletionFamily D L)
    (e : Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M D.Point ∞)
    (R : LiouvilleDomain 0)
    (eR : letI := R.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M R.domain.Point ∞)
    (E : Parameter → LiouvilleDomain 0) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain (E t).domain) :
    ∃ q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv
      (K t).ambient.manifold,
      (∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.pullback
        (K t).ambient.manifold (q t) (K t).ambient.primitive =
          (F.collars t).cylindricalCompletion.ambient.primitive) ∧
      (∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val) =
        (K t).inclusion.map ((h t).extensionEquiv (eR x).val)) ∧
      (∀ t x, (q t).symm ((K t).inclusion.map ((h t).extensionEquiv (eR x).val)) =
        (F.collars t).cylindricalCompletion.inclusion.map
          ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val) := by
  classical
  have slices (t : Parameter) :
      ∃ q : (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv
          (K t).ambient.manifold,
        (F.collars t).cylindricalCompletion.ambient.manifold.pullback
          (K t).ambient.manifold q (K t).ambient.primitive =
            (F.collars t).cylindricalCompletion.ambient.primitive ∧
        (∀ x, q ((F.collars t).cylindricalCompletion.inclusion.map
            ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val) =
          (K t).inclusion.map ((h t).extensionEquiv (eR x).val)) ∧
        (∀ x, q.symm ((K t).inclusion.map ((h t).extensionEquiv (eR x).val)) =
          (F.collars t).cylindricalCompletion.inclusion.map
            ((e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm) x).val) := by
    let := R.domain.zeroChartedSpace
    let := (E t).domain.zeroChartedSpace
    obtain ⟨q, hp, hs, hi, _⟩ :=
      exists_scaledEquiv_on_fixed_native_endpoints (F.collars t).localizedDomain (E t)
        (F.collars t).cylindricalCompletion (K t)
        (e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm)
        (eR.trans (h t).zeroNativePointDiffeomorph)
        (Diffeomorph.refl 𝓘(ℝ, Model 0) M ∞) 1
    exact ⟨q, by simpa only [one_smul] using hp, hs, hi⟩
  choose q hp hs hi using slices
  exact ⟨q, hp, hs, hi⟩

end FsFltz.Geometry.LocalizedCompletionFamily

namespace FsFltz.Geometry.IntrinsicZeroLiouville
open SmoothManifold

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (Model 0) M] [IsManifold 𝓘(ℝ, Model 0) ∞ M]

/-- Arbitrary original native zero-dimensional primitives construct a
localized completion family and actual strict comparisons with independent
prescribed moving completions. Both relative reference maps are jointly
smooth, their compact squares retain the original native points, and their
pullback identity uses the actual varying completed primitive.

The reference compact and completed presentations need not be normalized at
zero. No completion, collar or comparison regularity is assumed for the
constructed family; empty native sources are included. -/
theorem exists_strictMovingZeroNativeCompletionComparison
    (μ : Parameter → (sourceManifold M).Form 1)
    (R : LiouvilleDomain 0) (C : Completion R)
    (eR : letI := R.domain.zeroChartedSpace;
      Diffeomorph 𝓘(ℝ, Model 0) 𝓘(ℝ, Model 0) M R.domain.Point ∞)
    (E : Parameter → LiouvilleDomain 0) (K : ∀ t, Completion (E t))
    (h : ∀ t, DomainPresentationEquiv R.domain (E t).domain)
    (p : ∀ t, CompletionPresentationEquiv C (K t) (h t)) :
    ∃ (F : LocalizedCompletionFamily (compactDomain M) (liouvilleFamily μ))
      (q : ∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.SmoothEquiv
        (K t).ambient.manifold),
      (∀ t, (F.collars t).cylindricalCompletion.ambient.manifold.pullback
        (K t).ambient.manifold (q t) (K t).ambient.primitive =
          (F.collars t).cylindricalCompletion.ambient.primitive) ∧
      (∀ t x, q t ((F.collars t).cylindricalCompletion.inclusion.map
          ((carrierDiffeomorph (μ parameterZero)).trans
            (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm x).val) =
        (K t).inclusion.map ((h t).extensionEquiv (eR x).val)) ∧
      (∀ t x, (q t).symm ((K t).inclusion.map ((h t).extensionEquiv (eR x).val)) =
        (F.collars t).cylindricalCompletion.inclusion.map
          ((carrierDiffeomorph (μ parameterZero)).trans
            (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm x).val) ∧
      (∀ t x, F.referenceComparison C E K h p q t
          ((F.completionPresentation t).equiv.symm
            ((F.collars t).cylindricalCompletion.inclusion.map
              ((carrierDiffeomorph (μ parameterZero)).trans
                (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm x).val)) =
        C.inclusion.map (eR x).val) ∧
      (∀ t x, (F.referenceComparison C E K h p q t).symm (C.inclusion.map (eR x).val) =
        (F.completionPresentation t).equiv.symm
          ((F.collars t).cylindricalCompletion.inclusion.map
            ((carrierDiffeomorph (μ parameterZero)).trans
              (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm x).val)) ∧
      (F.collars parameterZero).cylindricalCompletion.ambient.manifold.IsSmoothIntervalMapFamily
        C.ambient.manifold (fun t => F.referenceComparison C E K h p q t) ∧
      C.ambient.manifold.IsSmoothIntervalMapFamily
        (F.collars parameterZero).cylindricalCompletion.ambient.manifold
        (fun t => (F.referenceComparison C E K h p q t).symm) ∧
      (∀ t, (F.collars parameterZero).cylindricalCompletion.ambient.manifold.pullback
        C.ambient.manifold (F.referenceComparison C E K h p q t)
        (C.ambient.manifold.pullback (K t).ambient.manifold (p t).equiv
          (K t).ambient.primitive) =
        (F.collars parameterZero).cylindricalCompletion.ambient.manifold.pullback
          (F.collars t).cylindricalCompletion.ambient.manifold
          (F.completionPresentation t).equiv
          (F.collars t).cylindricalCompletion.ambient.primitive) := by
  let F := localizedCompletionFamily μ
  let e := carrierDiffeomorph (μ parameterZero)
  obtain ⟨q, hp, hs, hi⟩ := F.exists_strictMovingZeroSliceComparisons e R eR E K h
  obtain ⟨hf, hfi⟩ := F.zeroReferenceComparison_smooth_of_native_square e R C eR E K h p q hs
  have hcompact (t : Parameter) (x : M) : F.referenceComparison C E K h p q t
      ((F.completionPresentation t).equiv.symm
        ((F.collars t).cylindricalCompletion.inclusion.map
          (e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm x).val)) =
      C.inclusion.map (eR x).val := by
    change (p t).equiv.symm (q t ((F.completionPresentation t).equiv
      ((F.completionPresentation t).equiv.symm _))) = _
    rw [(F.completionPresentation t).equiv.apply_symm_apply, hs,
      ← (p t).compact_square (eR x).val (eR x).property]
    exact (p t).equiv.symm_apply_apply _
  have hicompact (t : Parameter) (x : M) :
      (F.referenceComparison C E K h p q t).symm (C.inclusion.map (eR x).val) =
        (F.completionPresentation t).equiv.symm
          ((F.collars t).cylindricalCompletion.inclusion.map
            (e.trans (F.collars t).originalPointDiffeomorph_of_dimension_zero.symm x).val) := by
    exact (congrArg (F.referenceComparison C E K h p q t).symm (hcompact t x)).symm.trans
      ((F.referenceComparison C E K h p q t).symm_apply_apply _)
  refine ⟨F, q, hp, hs, hi, hcompact, hicompact, hf, hfi, ?_⟩
  intro t
  exact IntrinsicLiouville.relativeComparison_primitive C (K t)
    (F.collars parameterZero).cylindricalCompletion (F.collars t).cylindricalCompletion
    (h t) (p t) (F.compactPresentation t) (F.completionPresentation t) (q t) (hp t)

end FsFltz.Geometry.IntrinsicZeroLiouville
