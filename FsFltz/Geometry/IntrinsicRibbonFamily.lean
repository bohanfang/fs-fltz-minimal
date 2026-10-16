import FsFltz.Geometry.IntrinsicNativeIdentificationFamily
import FsFltz.Geometry.IntrinsicNativeMapFamily
import FsFltz.Geometry.IntrinsicRibbonPair
import FsFltz.Geometry.IntrinsicBoundaryWitnessFamily
import FsFltz.Geometry.IntrinsicNativeEndpointPresentation

/-!
# Native joint ribbon families on a fixed presented ambient boundary

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–160;
`def:chain`, lines 163–169; and `sec:lean`, lines 788–814.
Native joint map germs are glued on the very presentation carrying the
native primitive family. The bijective carrier differential transfers
immersion and the full witnessing primitive identity. A uniform embedding
neighborhood and the existing pair-family constructor provide an actual
`PairDeformation`, with both completed families. The full native ribbon
maps and the witnesses on the supplied ambient boundary are retained.

The ambient compact presentation and its Liouville family are supplied.
This foundation does not construct an arbitrary native ambient boundary
presentation, trivialize bundles, or prove the geometric target.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- The inclusion differential transfers native immersion in arbitrary
presentation dimensions; surjectivity is the only dimension fact used. -/
theorem injective_mfderiv_of_native_comp_on_presentation {r d : ℕ}
    (F : SmoothManifold r) (N : SmoothManifold d)
    (i : M → F.Point) (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) ∞ i)
    (hdi : ∀ x, Function.Surjective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x))
    (g : F.Point → N.Point) (hg : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, Model d) ∞ g)
    (j : M → N.Point) (heq : ∀ x, g (i x) = j x)
    (hdj : ∀ x, Function.Injective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) j x))
    (x : M) : Function.Injective (mfderiv 𝓘(ℝ, Model r) 𝓘(ℝ, Model d) g (i x)) := by
  have hd := mfderiv_comp (f := i) (g := g) x
    (hg.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [show g ∘ i = j from funext heq] at hd
  intro v w hvw
  obtain ⟨a, ha⟩ := hdi x v
  obtain ⟨b, hb⟩ := hdi x w
  have hab : a = b := hdj x (by
    rw [hd]
    change (mfderiv 𝓘(ℝ, Model r) 𝓘(ℝ, Model d) g (i x))
      ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) a) =
      (mfderiv 𝓘(ℝ, Model r) 𝓘(ℝ, Model d) g (i x))
      ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) b)
    rw [ha, hb]
    exact hvw)
  exact ha.symm.trans (hab ▸ hb)

/-- Native pullback determines the whole presentation one-form, including
all tangent directions at boundary points. -/
theorem pullback_eq_of_native_comp_on_presentation {r d : ℕ}
    (F : SmoothManifold r) (N : SmoothManifold d)
    (i : M → F.Point) (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) ∞ i)
    (hdi : ∀ x, Function.Surjective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x))
    (g : F.Point → N.Point) (hg : ContMDiff 𝓘(ℝ, Model r) 𝓘(ℝ, Model d) ∞ g)
    (j : M → N.Point) (heq : ∀ x, g (i x) = j x)
    (η : N.Form 1) (lam : F.Form 1) (α : Form k M 1)
    (hlam : ∀ x, (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) = α x)
    (hη : ∀ x, (η (j x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) j x) = α x)
    (x : M) : F.pullback N g η (i x) = lam (i x) := by
  have hd := mfderiv_comp (f := i) (g := g) x
    (hg.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp))
  rw [show g ∘ i = j from funext heq] at hd
  ext vs
  obtain ⟨v, hv⟩ := hdi x (vs 0)
  have he := congrArg (fun a => a (fun _ => v)) ((hη x).trans (hlam x).symm)
  rw [hd] at he
  change η (j x) (fun _ => (mfderiv 𝓘(ℝ, Model r) 𝓘(ℝ, Model d) g (i x))
    ((mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) v)) =
    lam (i x) (fun _ => (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) v) at he
  rw [hv, ← heq x] at he
  have hvs : (fun _ : Fin 1 => vs 0) = vs := by
    funext t
    exact congrArg vs (Fin.eq_zero t).symm
  rw [hvs] at he
  simpa only [SmoothManifold.pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, Fin.eq_zero] using he

variable [IsManifold (𝓡∂ (k + 1)) ∞ M] [CompactSpace M]

/-- Joint native map germs, native immersion and the full native witnessing
identity on a fixed ribbon primitive presentation construct an actual pair
family. Neither an extended map nor either completed family is supplied.
The native compact presentation remains explicit at every parameter. -/
theorem exists_pairDeformation_of_native_map_germs_with_native_coherence_and_coordinates {n : ℕ} [NeZero (2 * n - 2)] [NeZero n]
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (A : Parameter → LiouvilleStructure F)
    (i : M → F.extension.Point)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M F.Point ∞)
    (he : ∀ x, (e x).val = i x)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x))
    (hrange : range i = F.carrier)
    (hcoord : HasNativeCoordinateExtensions (k := k) F.extension i)
    (α : Parameter → Form k M 1)
    (hpull : ∀ t x, ((A t).primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x) = α t x)
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hA : F.extension.IsSmoothIntervalFormFamily (fun t => (A t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n,
      ∃ eA : ∀ t, Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point
        (Q.pair t).ambientDomain.domain.Point ∞,
      ∃ RA : ℝ → Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point D.Point ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (2 * n)) RA ∧
        (∀ t x, (Q.ambientPresentation t).extensionEquiv
          ((eA parameterZero (RA t.val x)).val) = (eA t x).val) ∧
      ∃ eB : ∀ t, D.boundary.SmoothEquiv (Q.pair t).ambientDomain.domain.boundary,
        (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eB parameterZero x) = eB t x) ∧
      ∃ eQ : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
        (Q.pair t).ribbonDomain.domain.Point ∞,
      ∃ R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R ∧
        (∀ t x, (Q.ribbonPresentation t).extensionEquiv
          ((eQ parameterZero (R t.val x)).val) = (eQ t x).val) ∧
      ∀ t : Parameter,
      ∃ C : LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
        (Q.pair t).ambientDomain = C.localizedDomain ∧
        HEq (eA t) C.originalPointDiffeomorph.symm ∧
        HEq (eB t) (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
        HEq aQ (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
        D.boundary.pullback (Q.pair t).ambientDomain.domain.boundary aQ.invFun
          ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
            D.boundaryForm (L t).primitive ∧
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ t x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ t y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ t x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ t y).val)} ∧
        HasNativeCoordinateExtensions (k := k)
          (Q.pair t).ribbonDomain.domain.extension (fun x => (eQ t x).val) := by
  obtain ⟨W, hW, g, hg, hgval⟩ :=
    exists_mapFamily_on_fixed_presentation F.extension i hemb hcoord D.boundary j hj
  have hcover : parameterInterval ×ˢ F.carrier ⊆ W := by rwa [← hrange]
  obtain ⟨U, V, hU, hV, hrect, f, hfval, hfs⟩ :=
    F.extension.exists_partialFamily_rectangle D.boundary F.carrier F.compact W hcover g hg
  let F₀ := F.restrict U hU
  let i₀ : M → F₀.extension.Point := fun x => ⟨i x, hU (hrange ▸ mem_range_self x)⟩
  have hi₀ : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i₀ :=
    (ContMDiff.subtypeVal_comp_iff U i₀).mp hi
  have hdi₀ (x : M) : mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i₀ x =
      mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x := by
    have hd := mfderiv_comp (f := i₀) (g := (Subtype.val : U → F.extension.Point)) x
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).mdifferentiableAt (by simp))
      (hi₀.mdifferentiableAt (by simp))
    erw [F.extension.mfderiv_restrict_val U (i₀ x)] at hd
    exact hd.symm
  have hsurj₀ (x : M) : Function.Surjective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i₀ x) := by
    rw [hdi₀]
    exact (hbij x).2
  have hrange₀ : range i₀ = F₀.carrier := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change i x ∈ F.carrier
      exact hrange ▸ mem_range_self x
    · intro hy
      obtain ⟨x, hx⟩ : y.val ∈ range i := hrange ▸ hy
      exact ⟨x, Subtype.ext hx⟩
  have hf (t : Parameter) : ContMDiff 𝓘(ℝ, Model (2 * n - 2))
      𝓘(ℝ, Model (2 * n - 1)) ∞ (f t.val) := by
    intro x
    exact ((hfs.contMDiffAt ((V.isOpen.prod isOpen_univ).mem_nhds
      (show (t.val, x) ∈ (V : Set ℝ) ×ˢ univ from ⟨hV t.property, mem_univ _⟩))).comp x
        (contMDiffAt_const.prodMk contMDiffAt_id))
  have hfj (t : Parameter) (x : M) : f t.val (i₀ x) = j t x :=
    (hfval t.val (hV t.property) (i₀ x)).trans (hgval t x _)
  have hfi : ∀ t ∈ parameterInterval, InjOn (f t) F₀.carrier := by
    intro t ht y hy z hz hyz
    rw [← hrange₀] at hy hz
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨c, rfl⟩ := hz
    exact congrArg i₀ (hinj ⟨t, ht⟩ ((hfj ⟨t, ht⟩ a).symm.trans
      (hyz.trans (hfj ⟨t, ht⟩ c))))
  have hfimm : ∀ t ∈ parameterInterval, ∀ x ∈ F₀.carrier, Function.Injective
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n - 1)) (f t) x) := by
    intro t ht y hy
    rw [← hrange₀] at hy
    obtain ⟨x, rfl⟩ := hy
    exact injective_mfderiv_of_native_comp_on_presentation F₀.extension D.boundary
      i₀ hi₀ hsurj₀ (f t) (hf ⟨t, ht⟩) (j ⟨t, ht⟩) (hfj ⟨t, ht⟩) (himm ⟨t, ht⟩) x
  have hpull₀ (t : Parameter) (x : M) :
      (((A t).restrict U hU).primitive (i₀ x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i₀ x) = α t x := by
    rw [(A t).restrict_primitive, hdi₀]
    exact hpull t x
  have hprimitive₀ : ∀ t : Parameter, ∀ x ∈ F₀.carrier,
      F₀.extension.pullback D.boundary (f t.val)
        (fun y => b t y • D.boundaryForm (L t).primitive y) x = ((A t).restrict U hU).primitive x := by
    intro t y hy
    rw [← hrange₀] at hy
    obtain ⟨x, rfl⟩ := hy
    exact pullback_eq_of_native_comp_on_presentation F₀.extension D.boundary i₀ hi₀ hsurj₀
      (f t.val) (hf t) (j t) (hfj t) _ _ (α t) (hpull₀ t) (hribbon t) x
  have hA₀ := F.extension.isSmoothIntervalFormFamily_restrict U (fun t => (A t).primitive) hA
  have hcover₀ : parameterInterval ×ˢ F₀.carrier ⊆ (V : Set ℝ) ×ˢ univ :=
    fun _ hp => ⟨hV hp.1, mem_univ _⟩
  obtain ⟨U₁, hU₁, q, hqval, hqs, _, _, _, _, hprimitive, ambient, ribbon, Q, hQ, hQdef⟩ :=
    D.exists_localized_pairDeformation_of_compactEmbeddingGerm_with_presentations F₀ L
      (fun t => (A t).restrict U hU) f ((V : Set ℝ) ×ˢ univ)
      (V.isOpen.prod isOpen_univ) hcover₀ hfs hfi hfimm b hL hA₀ hb hpositive hprimitive₀
  let := F₀.halfSpaceChartedSpace
  let := (F₀.restrict U₁ hU₁).halfSpaceChartedSpace
  let e₁ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (F₀.restrict U₁ hU₁).Point ∞ :=
    (e.trans (F.restrictPointDiffeomorph U hU).symm).trans
      (F₀.restrictPointDiffeomorph U₁ hU₁).symm
  have he₁ (x : M) : (e₁ x).val.val = i₀ x := Subtype.ext (he x)
  subst Q
  let C := ambient.collars
  let B := ribbon.collars
  let eQ := fun t : Parameter => e₁.trans (B t).originalPointDiffeomorph.symm
  let R := ribbon.transportedNativeDiffeomorph (𝓡∂ (k + 1)) e₁
  let Qassembled := D.localizedPairDeformation (F₀.restrict U₁ hU₁) L
    (fun t => ((A t).restrict U hU).restrict U₁ hU₁) q b hL
    (F₀.extension.isSmoothIntervalFormFamily_restrict U₁
      (fun t => ((A t).restrict U hU).primitive) hA₀)
    hqs hb hpositive ambient ribbon hprimitive
  let eA := fun t : Parameter => (C t).originalPointDiffeomorph.symm
  let RA := ambient.transportedNativeDiffeomorph (𝓡∂ (2 * n)) (Diffeomorph.refl _ D.Point ∞)
  let eB := fun _ : Parameter => (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞)
  refine ⟨Qassembled, eA, RA, ambient.jointlySmooth_transportedNativeDiffeomorph (𝓡∂ (2 * n)) (Diffeomorph.refl _ D.Point ∞),
    ambient.transportedNativeDiffeomorph_square (𝓡∂ (2 * n)) (Diffeomorph.refl _ D.Point ∞), eB, ?_,
    eQ, R, ribbon.jointlySmooth_transportedNativeDiffeomorph _ e₁,
    ribbon.transportedNativeDiffeomorph_square _ e₁, ?_⟩
  · intro t x
    change (ambient.compactPresentation t).boundaryEquiv x = x
    rw [ambient.boundary_compactPresentation]
    rfl
  · intro t
    let P := localizedWitnessedPair ⟨D, L t⟩
      ⟨F₀.restrict U₁ hU₁, ((A t).restrict U hU).restrict U₁ hU₁⟩
        (C t) (B t) (q t) (b t) (hb.contMDiff_slice t) (hpositive t) (hprimitive t)
    let eP : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M P.ribbonDomain.domain.Point ∞ :=
      e₁.trans (B t).originalPointDiffeomorph.symm
    have hjP (x : M) : P.ribbonEmbedding.map (eP x).val = j t x := by
      change (q t).map (eP x).val.val.val = _
      rw [hqval]
      change f t.val (e₁ x).val.val = _
      rw [he₁]
      exact hfj t x
    refine ⟨C t, rfl, HEq.rfl, HEq.rfl, (Diffeomorph.refl _ _ ∞), HEq.rfl, ?_, hjP, ?_, rfl, ?_, P.native_ribbon_primitive eP (α t) (j t) hjP ?_,
      ?_, ?_⟩
    · change D.boundary.pullback D.boundary id
        ((C t).localizedDomain.domain.boundaryForm (C t).localizedDomain.liouville.primitive) = _
      rw [(C t).localized_boundaryForm, D.boundary.pullback_id]
    · ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨x, hx⟩ := eP.surjective ⟨z, hz⟩
        exact ⟨x, (hjP x).symm.trans (congrArg (fun w => P.ribbonEmbedding.map w.val) hx)⟩
      · rintro ⟨x, rfl⟩
        exact ⟨(eP x).val, (eP x).property, hjP x⟩
    · intro y
      exact congrFun (C t).localized_boundaryForm y
    · change ∀ x, (b t (j t x) • (C t).localizedDomain.domain.boundaryForm
        (C t).localizedDomain.liouville.primitive (j t x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x
      rw [(C t).localized_boundaryForm]
      exact hribbon t
    · change id '' P.embeddedCore = _
      rw [image_id]
      exact P.embeddedCore_eq_native_image eP.toEquiv (j t) hjP
    · apply hcoord.of_smooth_square F.extension P.ribbonDomain.domain.extension i
        (fun x => (eP x).val)
        (fun z => ((B t).originalInclusion.map z).val.val)
        ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).comp
          ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).comp
            (B t).originalInclusion.map.contMDiff))
      intro x
      have hb := congrArg Subtype.val ((B t).originalPointDiffeomorph.apply_symm_apply (e₁ x))
      change (B t).originalInclusion.map (eP x).val = (e₁ x).val at hb
      change ((B t).originalInclusion.map (eP x).val).val.val = i x
      rw [hb]
      exact congrArg Subtype.val (he₁ x)

/-- The coherence interface forgetting only the retained endpoint coordinate germs. -/
theorem exists_pairDeformation_of_native_map_germs_with_native_coherence {n : ℕ} [NeZero (2 * n - 2)] [NeZero n]
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (A : Parameter → LiouvilleStructure F)
    (i : M → F.extension.Point)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M F.Point ∞)
    (he : ∀ x, (e x).val = i x)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x))
    (hrange : range i = F.carrier)
    (hcoord : HasNativeCoordinateExtensions (k := k) F.extension i)
    (α : Parameter → Form k M 1)
    (hpull : ∀ t x, ((A t).primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x) = α t x)
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hA : F.extension.IsSmoothIntervalFormFamily (fun t => (A t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n,
      ∃ eA : ∀ t, Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point
        (Q.pair t).ambientDomain.domain.Point ∞,
      ∃ RA : ℝ → Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point D.Point ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (2 * n)) RA ∧
        (∀ t x, (Q.ambientPresentation t).extensionEquiv
          ((eA parameterZero (RA t.val x)).val) = (eA t x).val) ∧
      ∃ eB : ∀ t, D.boundary.SmoothEquiv (Q.pair t).ambientDomain.domain.boundary,
        (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eB parameterZero x) = eB t x) ∧
      ∃ eQ : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
        (Q.pair t).ribbonDomain.domain.Point ∞,
      ∃ R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R ∧
        (∀ t x, (Q.ribbonPresentation t).extensionEquiv
          ((eQ parameterZero (R t.val x)).val) = (eQ t x).val) ∧
      ∀ t : Parameter,
      ∃ C : LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
        (Q.pair t).ambientDomain = C.localizedDomain ∧
        HEq (eA t) C.originalPointDiffeomorph.symm ∧
        HEq (eB t) (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
        HEq aQ (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
        D.boundary.pullback (Q.pair t).ambientDomain.domain.boundary aQ.invFun
          ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
            D.boundaryForm (L t).primitive ∧
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ t x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ t y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ t x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ t y).val)} := by
  obtain ⟨Q, eA, RA, hRA, hsquareA, eB, hsquareB, eQ, R, hR, hsquare, hQ⟩ :=
    exists_pairDeformation_of_native_map_germs_with_native_coherence_and_coordinates
      D F L A i e he hi hemb hbij hrange hcoord α hpull j hj hinj himm b hL hA hb hpositive hribbon
  refine ⟨Q, eA, RA, hRA, hsquareA, eB, hsquareB, eQ, R, hR, hsquare, ?_⟩
  intro t
  obtain ⟨C, hC, hEA, hEB, aQ, haQ, hB, hjQ, himage, hwitness, hboundary, hp, hcore, _⟩ := hQ t
  exact ⟨C, hC, hEA, hEB, aQ, haQ, hB, hjQ, himage, hwitness, hboundary, hp, hcore⟩

/-- Joint native map germs, native immersion and the full native witnessing
identity on a fixed ribbon primitive presentation construct an actual pair
family. Neither an extended map nor either completed family is supplied.
The native compact presentation remains explicit at every parameter. -/
theorem exists_pairDeformation_of_native_map_germs_with_ambient_collar {n : ℕ} [NeZero (2 * n - 2)]
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (A : Parameter → LiouvilleStructure F)
    (i : M → F.extension.Point)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M F.Point ∞)
    (he : ∀ x, (e x).val = i x)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x))
    (hrange : range i = F.carrier)
    (hcoord : HasNativeCoordinateExtensions (k := k) F.extension i)
    (α : Parameter → Form k M 1)
    (hpull : ∀ t x, ((A t).primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x) = α t x)
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hA : F.extension.IsSmoothIntervalFormFamily (fun t => (A t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n, ∀ t : Parameter,
      ∃ C : LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
        (Q.pair t).ambientDomain = C.localizedDomain ∧
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
        HEq aQ (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
        D.boundary.pullback (Q.pair t).ambientDomain.domain.boundary aQ.invFun
          ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
            D.boundaryForm (L t).primitive ∧
      ∃ eQ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (Q.pair t).ribbonDomain.domain.Point ∞,
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ y).val)} := by
  let : NeZero n := ⟨by intro hn; subst n; exact NeZero.ne (2 * 0 - 2) rfl⟩
  obtain ⟨Q, eA, RA, hRA, hsquareA, eB, hsquareB, eQ, R, hR, hsquare, hQ⟩ := exists_pairDeformation_of_native_map_germs_with_native_coherence
    D F L A i e he hi hemb hbij hrange hcoord α hpull j hj hinj himm
    b hL hA hb hpositive hribbon
  refine ⟨Q, ?_⟩
  intro t
  obtain ⟨C, hC, _, _, aQ, haQ, hboundary, hdata⟩ := hQ t
  exact ⟨C, hC, aQ, haQ, hboundary, eQ t, hdata⟩


/-- The original consumer forgets the actual ambient collar while retaining
all native ribbon and boundary identities. -/
theorem exists_pairDeformation_of_native_map_germs {n : ℕ} [NeZero (2 * n - 2)]
    (D : CompactDomain (2 * n)) (F : CompactDomain (2 * n - 2))
    (L : Parameter → LiouvilleStructure D) (A : Parameter → LiouvilleStructure F)
    (i : M → F.extension.Point)
    (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M F.Point ∞)
    (he : ∀ x, (e x).val = i x)
    (hi : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) ∞ i)
    (hemb : Topology.IsClosedEmbedding i)
    (hbij : ∀ x, Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x))
    (hrange : range i = F.carrier)
    (hcoord : HasNativeCoordinateExtensions (k := k) F.extension i)
    (α : Parameter → Form k M 1)
    (hpull : ∀ t x, ((A t).primitive (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) i x) = α t x)
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (hA : F.extension.IsSmoothIntervalFormFamily (fun t => (A t).primitive))
    (hb : D.boundary.IsSmoothIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n, ∀ t : Parameter,
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
      ∃ eQ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (Q.pair t).ribbonDomain.domain.Point ∞,
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ y).val)} := by
  obtain ⟨Q, hQ⟩ := exists_pairDeformation_of_native_map_germs_with_ambient_collar
    D F L A i e he hi hemb hbij hrange hcoord α hpull j hj hinj himm
    b hL hA hb hpositive hribbon
  refine ⟨Q, ?_⟩
  intro t
  obtain ⟨C, hC, aQ, _, _, eQ, hdata⟩ := hQ t
  exact ⟨aQ, eQ, hdata⟩

variable [T2Space M] [SecondCountableTopology M]

/-- Native jointly extendible ribbon primitives and maps, native Liouville
conditions and local boundary witness germs construct a pair deformation on
a supplied fixed ambient family. The spatial ribbon presentation, joint map
extension, both collar families and both completions are all produced.
Only interval-slice positivity/nondegeneracy/outwardness are required. -/
theorem exists_native_pairDeformation_on_fixed_ambient_with_native_coherence_and_coordinates {n : ℕ} [NeZero (2 * n - 2)] [NeZero n]
    (hdim : k + 1 = 2 * n - 2)
    (D : CompactDomain (2 * n)) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n,
      ∃ eA : ∀ t, Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point
        (Q.pair t).ambientDomain.domain.Point ∞,
      ∃ RA : ℝ → Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point D.Point ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (2 * n)) RA ∧
        (∀ t x, (Q.ambientPresentation t).extensionEquiv
          ((eA parameterZero (RA t.val x)).val) = (eA t x).val) ∧
      ∃ eB : ∀ t, D.boundary.SmoothEquiv (Q.pair t).ambientDomain.domain.boundary,
        (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eB parameterZero x) = eB t x) ∧
      ∃ eQ : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
        (Q.pair t).ribbonDomain.domain.Point ∞,
      ∃ R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R ∧
        (∀ t x, (Q.ribbonPresentation t).extensionEquiv
          ((eQ parameterZero (R t.val x)).val) = (eQ t x).val) ∧
      ∀ t : Parameter,
      ∃ C : LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
        (Q.pair t).ambientDomain = C.localizedDomain ∧
        HEq (eA t) C.originalPointDiffeomorph.symm ∧
        HEq (eB t) (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
        HEq aQ (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
        D.boundary.pullback (Q.pair t).ambientDomain.domain.boundary aQ.invFun
          ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
            D.boundaryForm (L t).primitive ∧
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ t x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ t y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ t x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ t y).val)} ∧
        HasNativeCoordinateExtensions (k := k)
          (Q.pair t).ribbonDomain.domain.extension (fun x => (eQ t x).val) := by
  have hpresentation : ∀ (r : ℕ) [NeZero r], k + 1 = r →
      ∃ (F : CompactDomain r) (i : M → F.extension.Point)
        (e : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ r) M F.Point ∞)
        (A : Parameter → LiouvilleStructure F),
        (∀ x, (e x).val = i x) ∧
        ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) ∞ i ∧
        Topology.IsClosedEmbedding i ∧
        (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x)) ∧
        range i = F.carrier ∧
        F.extension.IsSmoothIntervalFormFamily (fun t => (A t).primitive) ∧
        (∀ t x, ((A t).primitive (i x)).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model r) i x) = α t x) ∧
        HasNativeCoordinateExtensions (k := k) F.extension i := by
    intro r _ hr
    subst r
    obtain ⟨F, i, e, A, he, hi, hemb, hbij, hrange, _, hA, _, hpull, _, _, _, _, hcoord⟩ :=
      exists_liouvilleFamily_with_native_presentation_and_coordinates α hα hnd hout
    exact ⟨F, i, e, A, he, hi, hemb, hbij, hrange, hA,
      fun t x => congrFun (hpull t) x, hcoord⟩
  obtain ⟨F, i, e, A, he, hi, hemb, hbij, hrange, hA, hpull, hcoord⟩ :=
    hpresentation (2 * n - 2) hdim
  exact exists_pairDeformation_of_native_map_germs_with_native_coherence_and_coordinates D F L A i e he hi hemb hbij hrange
    hcoord α hpull j hj hinj himm b hL hA
      (D.boundary.isSmoothIntervalScalarFamily_of_local_germs b hb) hpositive hribbon



/-- The coherence interface forgetting only the retained endpoint coordinate germs. -/
theorem exists_native_pairDeformation_on_fixed_ambient_with_native_coherence {n : ℕ} [NeZero (2 * n - 2)] [NeZero n]
    (hdim : k + 1 = 2 * n - 2)
    (D : CompactDomain (2 * n)) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n,
      ∃ eA : ∀ t, Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point
        (Q.pair t).ambientDomain.domain.Point ∞,
      ∃ RA : ℝ → Diffeomorph (𝓡∂ (2 * n)) (𝓡∂ (2 * n)) D.Point D.Point ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (2 * n)) RA ∧
        (∀ t x, (Q.ambientPresentation t).extensionEquiv
          ((eA parameterZero (RA t.val x)).val) = (eA t x).val) ∧
      ∃ eB : ∀ t, D.boundary.SmoothEquiv (Q.pair t).ambientDomain.domain.boundary,
        (∀ t x, (Q.ambientPresentation t).boundaryEquiv (eB parameterZero x) = eB t x) ∧
      ∃ eQ : ∀ t, Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M
        (Q.pair t).ribbonDomain.domain.Point ∞,
      ∃ R : ℝ → Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (k + 1)) M M ∞,
        IsJointlySmoothDiffeomorphFamily (𝓡∂ (k + 1)) R ∧
        (∀ t x, (Q.ribbonPresentation t).extensionEquiv
          ((eQ parameterZero (R t.val x)).val) = (eQ t x).val) ∧
      ∀ t : Parameter,
      ∃ C : LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
        (Q.pair t).ambientDomain = C.localizedDomain ∧
        HEq (eA t) C.originalPointDiffeomorph.symm ∧
        HEq (eB t) (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
        HEq aQ (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
        D.boundary.pullback (Q.pair t).ambientDomain.domain.boundary aQ.invFun
          ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
            D.boundaryForm (L t).primitive ∧
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ t x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ t x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ t y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ t x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ t y).val)} := by
  obtain ⟨Q, eA, RA, hRA, hsquareA, eB, hsquareB, eQ, R, hR, hsquare, hQ⟩ :=
    exists_native_pairDeformation_on_fixed_ambient_with_native_coherence_and_coordinates
      hdim D L hL α hα hnd hout j hj hinj himm b hb hpositive hribbon
  refine ⟨Q, eA, RA, hRA, hsquareA, eB, hsquareB, eQ, R, hR, hsquare, ?_⟩
  intro t
  obtain ⟨C, hC, hEA, hEB, aQ, haQ, hB, hjQ, himage, hwitness, hboundary, hp, hcore, _⟩ := hQ t
  exact ⟨C, hC, hEA, hEB, aQ, haQ, hB, hjQ, himage, hwitness, hboundary, hp, hcore⟩

/-- Native jointly extendible ribbon primitives and maps, native Liouville
conditions and local boundary witness germs construct a pair deformation on
a supplied fixed ambient family. The spatial ribbon presentation, joint map
extension, both collar families and both completions are all produced.
Only interval-slice positivity/nondegeneracy/outwardness are required. -/
theorem exists_native_pairDeformation_on_fixed_ambient_with_ambient_collar {n : ℕ} [NeZero (2 * n - 2)]
    (hdim : k + 1 = 2 * n - 2)
    (D : CompactDomain (2 * n)) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n, ∀ t : Parameter,
      ∃ C : LiouvilleDomain.FlowCollar (⟨D, L t⟩ : LiouvilleDomain (2 * n)),
        (Q.pair t).ambientDomain = C.localizedDomain ∧
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
        HEq aQ (Diffeomorph.refl 𝓘(ℝ, Model (2 * n - 1)) D.boundary.Point ∞) ∧
        D.boundary.pullback (Q.pair t).ambientDomain.domain.boundary aQ.invFun
          ((Q.pair t).ambientDomain.domain.boundaryForm (Q.pair t).ambientDomain.liouville.primitive) =
            D.boundaryForm (L t).primitive ∧
      ∃ eQ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (Q.pair t).ribbonDomain.domain.Point ∞,
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ y).val)} := by
  let : NeZero n := ⟨by intro hn; subst n; exact NeZero.ne (2 * 0 - 2) rfl⟩
  obtain ⟨Q, eA, RA, hRA, hsquareA, eB, hsquareB, eQ, R, hR, hsquare, hQ⟩ :=
    exists_native_pairDeformation_on_fixed_ambient_with_native_coherence
      hdim D L hL α hα hnd hout j hj hinj himm b hb hpositive hribbon
  refine ⟨Q, ?_⟩
  intro t
  obtain ⟨C, hC, _, _, aQ, haQ, hboundary, hdata⟩ := hQ t
  exact ⟨C, hC, aQ, haQ, hboundary, eQ t, hdata⟩

/-- The original native fixed-ambient API is the projection of the stronger
producer retaining the ambient collar and its literal domain identity. -/
theorem exists_native_pairDeformation_on_fixed_ambient {n : ℕ} [NeZero (2 * n - 2)]
    (hdim : k + 1 = 2 * n - 2)
    (D : CompactDomain (2 * n)) (L : Parameter → LiouvilleStructure D)
    (hL : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive))
    (α : Parameter → Form k M 1) (hα : IsLocallyExtendibleFormFamily α)
    (hnd : ∀ t x, Nondegenerate (exteriorDerivative (α t)) x)
    (hout : ∀ t (x : IntrinsicBoundary.Point k M),
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector (α t) (exteriorDerivative (α t)) x.val)))
    (j : Parameter → M → D.boundary.Point)
    (hj : IsLocallyExtendibleMapFamily (k := k) D.boundary j)
    (hinj : ∀ t, Function.Injective (j t))
    (himm : ∀ t x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x))
    (b : Parameter → D.boundary.Point → ℝ)
    (hb : D.boundary.IsLocallyExtendibleIntervalScalarFamily b)
    (hpositive : ∀ t x, 0 < b t x)
    (hribbon : ∀ t x, (b t (j t x) • D.boundaryForm (L t).primitive (j t x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 1)) (j t) x) = α t x) :
    ∃ Q : PairDeformation n, ∀ t : Parameter,
      ∃ aQ : (Q.pair t).ambientDomain.domain.boundary.SmoothEquiv D.boundary,
      ∃ eQ : Diffeomorph (𝓡∂ (k + 1)) (𝓡∂ (2 * n - 2)) M (Q.pair t).ribbonDomain.domain.Point ∞,
        (∀ x, aQ ((Q.pair t).ribbonEmbedding.map (eQ x).val) = j t x) ∧
        (aQ ∘ (Q.pair t).ribbonEmbedding.map) '' (Q.pair t).ribbonDomain.domain.carrier = range (j t) ∧
        (fun y => (Q.pair t).witness (aQ.invFun y)) = b t ∧
        (∀ y, (Q.pair t).ambientDomain.domain.boundaryForm
          (Q.pair t).ambientDomain.liouville.primitive (aQ.invFun y) =
            D.boundaryForm (L t).primitive y) ∧
        (∀ x, ((Q.pair t).ribbonDomain.liouville.primitive (eQ x).val).compContinuousLinearMap
          (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (2 * n - 2)) (fun y => (eQ y).val) x) = α t x) ∧
        aQ '' (Q.pair t).embeddedCore = j t '' {x | ∀ s : ℝ, 0 ≤ s →
          (Q.pair t).ribbonCompletion.ambient.completeFlow.flow s
            ((Q.pair t).ribbonCompletion.inclusion.map (eQ x).val) ∈
              range (fun y => (Q.pair t).ribbonCompletion.inclusion.map (eQ y).val)} := by
  obtain ⟨Q, hQ⟩ := exists_native_pairDeformation_on_fixed_ambient_with_ambient_collar
    hdim D L hL α hα hnd hout j hj hinj himm b hb hpositive hribbon
  refine ⟨Q, ?_⟩
  intro t
  obtain ⟨C, hC, aQ, _, _, eQ, hdata⟩ := hQ t
  exact ⟨aQ, eQ, hdata⟩

end FsFltz.Geometry.IntrinsicLiouville
