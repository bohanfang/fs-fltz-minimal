import FsFltz.Geometry.IntrinsicNativePairFamily
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation
import FsFltz.Geometry.IntrinsicPresentationCollarComparison
import FsFltz.Geometry.PrescribedFamilyCollarGerms
import FsFltz.Geometry.IntrinsicNativeJointCollar
import FsFltz.Geometry.IntrinsicCompletionFamilyDescent

/-!
# Native cylinders on the same completed pair family

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 142–158;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–793 and 805–814.
The original native inward Liouville trajectories agree with the actual
completion end trajectories. The native primitive and coordinate squares
on already fixed compact endpoints determine this equality. Boundary
coherence then identifies the same trajectories in the fixed completed
presentation of an actual pair deformation. Its completed primitive
regularity produces one real jointly smooth cylinder extension, including
the parameter endpoints, a small inward strip and every outward radius.

These are completion-family foundation lemmas. They assert no geometric
comparison chain, full-fiber marking, endpoint core equality or grading.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- A native inward trajectory on an already fixed compact endpoint maps
to that endpoint's actual negative-radius end. The supplied boundary map
is identified from its inclusion square; no collar square is assumed. -/
theorem completed_native_inward_eq_endMap
    (hdim : k + 1 = d) (D : LiouvilleDomain d) (K : Completion D)
    (α : Form k M 1)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M D.domain.Point ∞)
    (hp : ∀ x, (D.liouville.primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (e y).val) x) = α x)
    (hc : HasNativeCoordinateExtensions (k := k) D.domain.extension (fun x => (e x).val))
    (b : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary)
    (hb : ∀ x, D.domain.boundaryInclusion.map (b x) = (e x.val).val)
    {γ : ℝ → M} {δ : ℝ} (x : IntrinsicBoundary.Point k M)
    (hγ : IsMIntegralCurveOn γ
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (hzero : γ 0 = x.val) (s : ℝ) (hs : s ∈ Ico 0 δ) :
    K.inclusion.map (e (γ s)).val = K.endMap (b x, -s) := by
  subst d
  let P := NativeLiouvillePresentation.of_endpoint α D e hp hc
  have hboundary : b x = P.nativeBoundaryEquiv x := by
    apply D.domain.boundaryInclusion.embedding.injective
    exact (hb x).trans (P.nativeBoundaryEquiv_inclusion x).symm
  rw [hboundary]
  exact P.completed_inclusion_eq_negative_flow K x hγ hzero s hs

end FsFltz.Geometry.IntrinsicLiouville

namespace FsFltz.Geometry.CompletionPresentationEquiv
open IntrinsicLiouville

variable {k d : ℕ} [NeZero d] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- Boundary coherence identifies the actual native inward cylinder in
the already specified fixed completion presentation. This applies to
either the ambient or the positive-dimensional ribbon completion. -/
theorem native_inward_reference_square
    (hdim : k + 1 = d) {D E : LiouvilleDomain d}
    {C : Completion D} {K : Completion E}
    {h : DomainPresentationEquiv D.domain E.domain}
    (p : CompletionPresentationEquiv C K h)
    (α : Form k M 1)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ d) M E.domain.Point ∞)
    (hp : ∀ x, (E.liouville.primitive (e x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) (fun y => (e y).val) x) = α x)
    (hc : HasNativeCoordinateExtensions (k := k) E.domain.extension (fun x => (e x).val))
    (b₀ : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv D.domain.boundary)
    (b : (IntrinsicBoundary.smoothManifold k M).SmoothEquiv E.domain.boundary)
    (hb : ∀ x, E.domain.boundaryInclusion.map (b x) = (e x.val).val)
    (hsquare : ∀ x, h.boundaryEquiv (b₀ x) = b x)
    {γ : ℝ → M} {δ : ℝ} (x : IntrinsicBoundary.Point k M)
    (hγ : IsMIntegralCurveOn γ
      (fun z => -liouvilleVector α (exteriorDerivative α) z) (Ico 0 δ))
    (hzero : γ 0 = x.val) (s : ℝ) (hs : s ∈ Ico 0 δ) :
    p.equiv.symm (K.inclusion.map (e (γ s)).val) =
      p.prescribedEndMap (b₀ x, -s) := by
  rw [completed_native_inward_eq_endMap hdim E K α e hp hc b hb x hγ hzero s hs]
  change p.equiv.symm (K.endMap (b x, -s)) =
    p.equiv.symm (K.endMap (h.boundaryEquiv (b₀ x), -s))
  rw [hsquare]

end FsFltz.Geometry.CompletionPresentationEquiv

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The actual native compact inclusion in the fixed completed ambient
presentation of this very pair deformation. -/
def ambientNativeReferenceMap (Q : PairDeformation n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (t : Parameter) (x : M) :
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point :=
  (Q.ambientCompletionPresentation t).equiv.symm
    ((Q.pair t).ambientCompletion.inclusion.map (e t x).val)

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- The retained native compact coherence square gives the actual compact
formula in the fixed completed presentation, on every original point. -/
theorem ambientNativeReferenceMap_eq_compact
    (Q : PairDeformation n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hsquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    (t : Parameter) (x : M) :
    Q.ambientNativeReferenceMap e t x =
      (Q.pair parameterZero).ambientCompletion.inclusion.map
        (e parameterZero (R t.val x)).val := by
  have h := (Q.ambientCompletionPresentation t).compact_square
    (e parameterZero (R t.val x)).val (e parameterZero (R t.val x)).property
  rw [hsquare] at h
  change (Q.ambientCompletionPresentation t).equiv.symm
    ((Q.pair t).ambientCompletion.inclusion.map (e t x).val) = _
  rw [← h, (Q.ambientCompletionPresentation t).equiv.symm_apply_apply]

omit [T2Space M] [SecondCountableTopology M] [IsManifold (𝓡∂ (k + 1)) ∞ M] in
/-- Joint native compact coherence proves continuity of the native map
into the same fixed completion. No completed map regularity is assumed. -/
theorem continuous_ambientNativeReferenceMap
    (Q : PairDeformation n)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquare : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val) :
    Continuous (fun p : Parameter × M => Q.ambientNativeReferenceMap e p.1 p.2) := by
  have hnative : Continuous (fun p : Parameter × M => R p.1.val p.2) :=
    hR.1.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hfixed : Continuous (fun x : M =>
      (Q.pair parameterZero).ambientCompletion.inclusion.map (e parameterZero x).val) :=
    (Q.pair parameterZero).ambientCompletion.inclusion.map.contMDiff.continuous.comp
      (continuous_subtype_val.comp (e parameterZero).contMDiff.continuous)
  convert hfixed.comp hnative using 1
  funext p
  exact Q.ambientNativeReferenceMap_eq_compact e R hsquare p.1 p.2

/-- The natural inward cylinder square uses the exact completed family
and the retained native boundary identifications. Primitive and coordinate
premises are compact endpoint conclusions of the native family producer. -/
theorem ambientNativeReferenceMap_collar
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (α : Parameter → Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquare : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    {δ : ℝ} (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
      (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
    (hzero : ∀ t x, C t (0, x) = x.val)
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (s : ℝ) (hs : s ∈ Ico 0 δ) :
    Q.ambientNativeReferenceMap e t (C t (s, x)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero x, -s) :=
  (Q.ambientCompletionPresentation t).native_inward_reference_square hdim
    (α t) (e t) (hp t) (hc t) (b parameterZero) (b t) (hb t) (hsquare t)
    x (hode t x) (hzero t x) s hs

/-- One real jointly smooth cylinder formula extends the same native
inward cylinder and every outward end of the original pair deformation.
Matching is asserted on actual interval parameters, with the inward sign
`r = -s`, above a uniform negative cutoff. -/
theorem exists_ambientNativeCylinderFamily_extension
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (α : Parameter → Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquare : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    {δ : ℝ} (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
      (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
    (hzero : ∀ t x, C t (0, x) = x.val) :
    ∃ a : ℝ, a < 0 ∧
      ∃ β : ℝ → IntrinsicBoundary.Point k M × ℝ →
          (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point,
        ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
          𝓘(ℝ, Model (2 * n)) ∞ (fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β q.1 q.2) ∧
        (∀ (t : Parameter) x r, a < r →
          β t.val (x, r) =
            (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero x, r)) ∧
        (∀ (t : Parameter) x s, s ∈ Ico 0 δ → a < -s →
          β t.val (x, -s) = Q.ambientNativeReferenceMap e t (C t (s, x))) ∧
        ∀ (t : Parameter) x r, 0 ≤ r →
          β t.val (x, r) = (Q.pair parameterZero).ambientCompletion.endMap (b parameterZero x, r) := by
  obtain ⟨a, ha, γ, hγ, heγ⟩ :=
    (Q.pair parameterZero).ambientCompletion.exists_prescribedFamily_end_strip_extension
      (fun t => (Q.pair t).ambientDomain) (fun t => (Q.pair t).ambientCompletion)
      Q.ambientPresentation Q.ambientCompletionPresentation Q.completedAmbientPrimitive_smooth
  let β := fun s (p : IntrinsicBoundary.Point k M × ℝ) => γ s (b parameterZero p.1, p.2)
  have hβ : ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, Model (2 * n)) ∞ (fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β q.1 q.2) := by
    have hb₀ := (b parameterZero).contMDiff
    exact hγ.comp (contMDiff_fst.prodMk
      ((hb₀.comp (contMDiff_fst.comp contMDiff_snd)).prodMk
        (contMDiff_snd.comp contMDiff_snd)))
  refine ⟨a, ha, β, hβ, ?_, ?_, ?_⟩
  · intro t x r hr
    exact heγ t (b parameterZero x) r hr
  · intro t x s hs hsa
    exact (heγ t (b parameterZero x) (-s) hsa).trans
      (Q.ambientNativeReferenceMap_collar hdim α e hp hc b hb hsquare C hode hzero t x s hs).symm
  · intro t x r hr
    exact (heγ t (b parameterZero x) r (lt_of_lt_of_le ha hr)).trans
      ((Q.ambientCompletionPresentation t).prescribedEndMap_nonnegative _ r hr)

/-- Original native family data construct the actual inward collar and
its exact square with the already fixed completed pair family. The same
completed primitive family constructs the real extension. The original
collar width is retained, and its full inward square has no cutoff. -/
theorem exists_ambientNativeCylinderFamily_of_native_data [CompactSpace M]
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (eta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧ (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ eta
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        eta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquare : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x) :
    ∃ (δ : ℝ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M),
      0 < δ ∧
      IsOpenEmbedding (fun p : Ico 0 δ ×ˢ (univ : Set (Parameter × IntrinsicBoundary.Point k M)) =>
        (p.val.2.1, C p.val.2.1 (p.val.1, p.val.2.2))) ∧
      (∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t) (Ico 0 δ ×ˢ univ)) ∧
      (∀ t x, C t (0, x) = x.val) ∧
      (∀ t x s, s ∈ Ico 0 δ → ((𝓡∂ (k + 1)).IsBoundaryPoint (C t (s, x)) ↔ s = 0)) ∧
      (∀ t, IsOpenEmbedding (fun p : Ico 0 δ ×ˢ univ => C t p.val)) ∧
      (∀ t p, p ∈ Ico 0 δ ×ˢ univ →
        ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
          ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
          ∀ᶠ q in 𝓝[Ico 0 δ ×ˢ univ] p, g (C t q) = q) ∧
      (∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
        (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ)) ∧
      (∀ (t : Parameter) x s, s ∈ Ico 0 δ →
        Q.ambientNativeReferenceMap e t (C t (s, x)) =
          (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero x, -s)) ∧
      ∃ a : ℝ, a < 0 ∧
        ∃ β : ℝ → IntrinsicBoundary.Point k M × ℝ →
            (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point,
          ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
            𝓘(ℝ, Model (2 * n)) ∞ (fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β q.1 q.2) ∧
          (∀ (t : Parameter) x r, a < r →
            β t.val (x, r) = (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero x, r)) ∧
          (∀ (t : Parameter) x s, s ∈ Ico 0 δ → a < -s →
            β t.val (x, -s) = Q.ambientNativeReferenceMap e t (C t (s, x))) ∧
          ∀ (t : Parameter) x r, 0 ≤ r →
            β t.val (x, r) = (Q.pair parameterZero).ambientCompletion.endMap (b parameterZero x, r) := by
  obtain ⟨δ, C, hδ, hjoint, hC, hzero, hboundary, hemb, hinv, hode, _⟩ :=
    exists_uniform_native_joint_collar α hα hnd hout
  refine ⟨δ, C, hδ, hjoint, hC, hzero, hboundary, hemb, hinv, hode, ?_, ?_⟩
  · intro t x s hs
    exact Q.ambientNativeReferenceMap_collar hdim α e hp hc b hb hsquare C hode hzero t x s hs
  · exact Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquare C hode hzero

end FsFltz.Geometry.PairDeformation

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- The natural native and cylindrical maps descend continuously from the
original shared quotient to the fixed completed ambient of the same pair
family. Its original collar width is unchanged. Near the seam and on the
whole outward end, continuity follows from the constructed real extension;
on the remaining inward cylinder it follows from the original native map. -/
theorem exists_continuous_ambientNativeTotalMap
    (Q : PairDeformation n) (hdim : k + 1 = 2 * n)
    (α : Parameter → Form k M 1)
    (e : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n)) M
      (Q.pair t).ambientDomain.domain.Point ∞)
    (hp : ∀ t x, ((Q.pair t).ambientDomain.liouville.primitive (e t x).val).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n)) (fun y => (e t y).val) x) = α t x)
    (hc : ∀ t, HasNativeCoordinateExtensions (k := k)
      (Q.pair t).ambientDomain.domain.extension (fun x => (e t x).val))
    (b : ∀ t, (IntrinsicBoundary.smoothManifold k M).SmoothEquiv
      (Q.pair t).ambientDomain.domain.boundary)
    (hb : ∀ t x, (Q.pair t).ambientDomain.domain.boundaryInclusion.map (b t x) = (e t x.val).val)
    (hsquareB : ∀ t x, (Q.ambientPresentation t).boundaryEquiv (b parameterZero x) = b t x)
    (R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞)
    (hR : IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R)
    (hsquareA : ∀ t x, (Q.ambientPresentation t).extensionEquiv
      (e parameterZero (R t.val x)).val = (e t x).val)
    {δ : ℝ} (hδ : 0 < δ) (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (hjoint : IsOpenEmbedding (totalCollar
      (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
    (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
      (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
    (hzero : ∀ t x, C t (0, x) = x.val) :
    let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
    ∃ q : TotalSpace c → (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point,
      Continuous q ∧
      (∀ t x, q (original (totalCollar c) (t, x)) = Q.ambientNativeReferenceMap e t x) ∧
      ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
        q (totalCylinder c (t, p)) =
          (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1) := by
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let f := fun p : Parameter × M => Q.ambientNativeReferenceMap e p.1 p.2
  let g := fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
    (Q.ambientCompletionPresentation p.1).prescribedEndMap (b parameterZero p.2.val.2, -p.2.val.1)
  have hseam (t : Parameter) (p : Half δ (IntrinsicBoundary.Point k M)) :
      f (t, c t p) = g (t, halfToBand p) :=
    Q.ambientNativeReferenceMap_collar hdim α e hp hc b hb hsquareB C hode hzero
      t p.val.2 p.val.1 p.property.1
  obtain ⟨a, ha, β, hβ, heβ, _, _⟩ :=
    Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquareB C hode hzero
  have hβcontinuous : Continuous (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
      β p.1.val (p.2.val.2, -p.2.val.1)) :=
    hβ.continuous.comp (show Continuous
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
        (p.1.val, (p.2.val.2, -p.2.val.1))) from by fun_prop)
  have hg : ContinuousOn g {p | p.2.val.1 < -a} := by
    apply hβcontinuous.continuousOn.congr
    intro p hp'
    exact (heβ p.1 p.2.val.2 (-p.2.val.1)
      (by change p.2.val.1 < -a at hp'; linarith)).symm
  refine ⟨totalDescendMap c f g, ?_, ?_, ?_⟩
  · exact continuous_totalDescendMap_of_end_strip c f g hseam hδ hjoint.continuous
      (Q.continuous_ambientNativeReferenceMap e R hR hsquareA) (neg_pos.mpr ha) hg
  · intro t x
    exact totalDescendMap_original c f g t x
  · intro t p
    exact totalDescendMap_cylinder c f g hseam (t, p)

end FsFltz.Geometry.PairDeformation
