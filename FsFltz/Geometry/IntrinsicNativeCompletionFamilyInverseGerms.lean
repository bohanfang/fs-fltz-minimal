import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverseSmooth

/-!
# Real inverse germs of the original completed comparison

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. The real inverse witnesses needed to transport
prescribed grading coefficients are retained, with their literal agreement
with the inverse of the original completion quotient comparison.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry.IntrinsicCompletionGluing

/-- The real inverse of a parameter-retaining cylinder comparison remains
parameter-retaining on a genuine open neighborhood. Its interval restriction
is the inverse of the same original quotient comparison. -/
theorem exists_realInverseGerm_of_cylinder
    {k d : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
    [IsManifold (𝓡∂ (k + 1)) ∞ M]
    {δ : ℝ} (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
    (N : SmoothManifold d)
    (A : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) ≃
      Parameter × N.Point)
    (β : ℝ → IntrinsicBoundary.Point k M × ℝ → N.Point)
    (a : ℝ)
    (hsquare : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      a < -p.val.1 → A (totalCylinder (fun t p => C t p.val) (t, p)) =
        (t, β t.val (p.val.2, -p.val.1)))
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ)
    (hr : a < r) (hrδ : -r < δ)
    (hl : IsLocalDiffeomorphAt
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) ∞
      (fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (q.1, β q.1 q.2))
      (t.val, (x, r))) :
    ∃ U : Set (ℝ × N.Point), IsOpen U ∧ (t.val, β t.val (x, r)) ∈ U ∧
      ∃ g : ℝ × N.Point → IntrinsicBoundary.Point k M × ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U ∧
        g (t.val, β t.val (x, r)) = (x, r) ∧
        (∃ l : PartialDiffeomorph
            ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
            ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
            (ℝ × N.Point) (ℝ × (IntrinsicBoundary.Point k M × ℝ)) ∞,
          U ⊆ l.source ∧ ∀ z ∈ U, l z = (z.1, g z)) ∧
        (∀ z ∈ U, a < (g z).2 ∧ -(g z).2 < δ ∧ β z.1 (g z) = z.2) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          ∃ p : Band δ (IntrinsicBoundary.Point k M),
            p.val = (-(g (s.val, y)).2, (g (s.val, y)).1) ∧
            A.symm (s, y) = totalCylinder (fun t p => C t p.val) (s, p) := by
  let G := fun q : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (q.1, β q.1 q.2)
  let V : Set (ℝ × (IntrinsicBoundary.Point k M × ℝ)) :=
    {q | a < q.2.2 ∧ -q.2.2 < δ}
  have hV : IsOpen V := (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).inter
    (isOpen_lt (continuous_snd.comp continuous_snd).neg continuous_const)
  let U := hl.localInverse.source ∩ hl.localInverse ⁻¹' V
  have hU : IsOpen U := hl.localInverse_contMDiffOn.continuousOn.isOpen_inter_preimage
    hl.localInverse.open_source hV
  have hpU : (t.val, β t.val (x, r)) ∈ U := by
    refine ⟨hl.localInverse_mem_source, ?_⟩
    change hl.localInverse (G (t.val, (x, r))) ∈ V
    rw [hl.localInverse_left_inv hl.localInverse_mem_target]
    exact ⟨hr, hrδ⟩
  let g := fun z : ℝ × N.Point => (hl.localInverse z).2
  have hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d))
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U :=
    contMDiff_snd.comp_contMDiffOn (hl.localInverse_contMDiffOn.mono inter_subset_left)
  have hgp : g (t.val, β t.val (x, r)) = (x, r) :=
    congrArg Prod.snd (hl.localInverse_left_inv hl.localInverse_mem_target)
  have hgU : ∀ z ∈ U, a < (g z).2 ∧ -(g z).2 < δ ∧ β z.1 (g z) = z.2 := by
    intro z hz
    have he := hl.localInverse_right_inv hz.1
    have ht : (hl.localInverse z).1 = z.1 := congrArg Prod.fst he
    refine ⟨hz.2.1, hz.2.2, ?_⟩
    have hs := congrArg Prod.snd he
    change β (hl.localInverse z).1 (g z) = z.2 at hs
    rwa [ht] at hs
  have hlU : ∀ z ∈ U, hl.localInverse z = (z.1, g z) := by
    intro z hz
    apply Prod.ext
    · have ht : (hl.localInverse z).1 = z.1 :=
        congrArg Prod.fst (hl.localInverse_right_inv hz.1)
      exact ht
    · rfl
  refine ⟨U, hU, hpU, g, hg, hgp, ⟨hl.localInverse, inter_subset_left, hlU⟩, hgU, ?_⟩
  intro s y hy
  refine ⟨⟨(-(g (s.val, y)).2, (g (s.val, y)).1), (hgU _ hy).2.1, mem_univ _⟩,
    rfl, ?_⟩
  apply A.injective
  rw [A.apply_symm_apply, hsquare s _ (by simpa only [neg_neg] using (hgU _ hy).1)]
  apply Prod.ext
  · rfl
  · simpa only [neg_neg] using (hgU _ hy).2.2.symm

end FsFltz.Geometry.IntrinsicCompletionGluing

namespace FsFltz.Geometry.PairDeformation
open IntrinsicLiouville IntrinsicCompletionGluing

variable {k n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
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
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t x, C t (0, x) = x.val)
  (hjoint : IsOpenEmbedding (totalCollar
    (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val)))
  (hmix : HasRealMixedGerms (δ := δ) C)
  (hode : ∀ t x, IsMIntegralCurveOn (fun s => C t (s, x))
    (fun z => -liouvilleVector (α t) (exteriorDerivative (α t)) z) (Ico 0 δ))
  (q : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) →
    (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point)
  (hqnative : ∀ t x,
    q (original (totalCollar (fun t p => C t p.val)) (t, x)) = Q.ambientNativeReferenceMap e t x)
  (hqend : ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    q (totalCylinder (fun t p => C t p.val) (t, p)) =
      (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.val.2, -p.val.1))


include hdim α hp hc hb hsquareB hzero hode in
/-- Every point of the original reference end, including radius zero and
both parameter endpoints, has a real parameter-preserving inverse germ.
The germ is a partial diffeomorphism, and its interval values are literally
the inverse of the original total comparison on the original cylinder. -/
theorem exists_ambientNativeTotalEquiv_symm_realEndGerm
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ U ∧
      ∃ g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U ∧
        g (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) = (x, r) ∧
        (∃ l : PartialDiffeomorph
            ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
            ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
            (ℝ × Q.source.ambientCompletion.ambient.manifold.Point)
            (ℝ × (IntrinsicBoundary.Point k M × ℝ)) ∞,
          U ⊆ l.source ∧ ∀ z ∈ U, l z = (z.1, g z)) ∧
        (∀ z ∈ U, -(g z).2 < δ) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          ∃ p : Band δ (IntrinsicBoundary.Point k M),
            p.val = (-(g (s.val, y)).2, (g (s.val, y)).1) ∧
            (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
              totalCylinder (fun t p => C t p.val) (s, p) := by
  obtain ⟨a, ha, β, hβ, heβ, _, hβend⟩ :=
    Q.exists_ambientNativeCylinderFamily_extension hdim α e hp hc b hb hsquareB C hode hzero
  let c := fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val
  let := bandChartedSpace (k := k) (B := IntrinsicBoundary.Point k M) δ
  let B := (b parameterZero).prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  have hl₀ : IsLocalDiffeomorphAt
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n)) ∞
      (fun p : IntrinsicBoundary.Point k M × ℝ =>
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.1, p.2))
      (x, r) :=
    (B.isLocalDiffeomorph (x, r)).comp 𝓘(ℝ, Model (2 * n))
      (Q.pair parameterZero).ambientCompletion.ambient.manifold.Point
      ((Q.ambientCompletionPresentation t).isLocalDiffeomorph_prescribedEndMap (B (x, r)))
  have heq : (fun p : IntrinsicBoundary.Point k M × ℝ => β t.val p) =ᶠ[𝓝 (x, r)]
      (fun p : IntrinsicBoundary.Point k M × ℝ =>
        (Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero p.1, p.2)) := by
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (show r ∈ Ioi a from lt_of_lt_of_le ha hr))] with p hp'
    exact heβ t p.1 p.2 hp'
  have hbij : Function.Bijective (mfderiv
      ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, Model (2 * n))
      (fun p : IntrinsicBoundary.Point k M × ℝ => β t.val p) (x, r)) := by
    rw [heq.mfderiv_eq]
    exact (tangentSpaceCast 𝓘(ℝ, Model (2 * n))
      ((Q.ambientCompletionPresentation t).prescribedEndMap (b parameterZero x, r))
      (β t.val (x, r))).bijective.comp
        ((hl₀.mfderivToContinuousLinearEquiv (by simp)).bijective)
  have hl : IsLocalDiffeomorphAt
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) ∞
      (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => (p.1, β p.1 p.2))
      (t.val, (x, r)) := by
    have hM : IsManifold ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞
        (IntrinsicBoundary.Point k M × ℝ) := inferInstance
    let : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
      prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
    rw [← modelWithCornersSelf_prod] at hM hβ hbij ⊢
    exact isLocalDiffeomorphAt_parameterMap_of_bijective_slice
      (fun p : ℝ × (IntrinsicBoundary.Point k M × ℝ) => β p.1 p.2) hβ t.val (x, r) hbij
  have hsquare : ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      a < -p.val.1 →
      Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend (totalCylinder c (s, p)) =
        (s, β s.val (p.val.2, -p.val.1)) := by
    intro s p hp'
    apply Prod.ext
    · rfl
    · exact (hqend s p).trans (heβ s p.val.2 (-p.val.1) hp').symm
  obtain ⟨U, hU, hpU, g, hg, hgp, hlift, hrange, heq⟩ :=
    exists_realInverseGerm_of_cylinder C Q.source.ambientCompletion.ambient.manifold
      (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend)
      β a hsquare t x r (lt_of_lt_of_le ha hr) (by linarith) hl
  rw [hβend t x r hr] at hpU hgp
  exact ⟨U, hU, hpU, g, hg, hgp, hlift, fun z hz => (hrange z hz).2.1, heq⟩

include hdim hR in
/-- The original compact-interior inverse has a real smooth spatial germ,
using the original native relabeling family and the fixed reference inclusion.
Its restriction to every nearby interval point is the original total inverse. -/
theorem exists_ambientNativeTotalEquiv_symm_realInteriorGerm
    (t : Parameter) (u : IntrinsicInterior.Point k M) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.ambientNativeInteriorReferenceMap (e parameterZero) u) ∈ U ∧
      ∃ g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicInterior.Point k M,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          𝓘(ℝ, Model (k + 1)) ∞ g U ∧
        (g (t.val, Q.ambientNativeInteriorReferenceMap (e parameterZero) u)).val =
          (R t.val).symm u.val ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
            totalInterior (fun t p => C t p.val) (s, g (s.val, y)) := by
  let A := Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend
  let f := Q.ambientNativeInteriorReferenceMap (e parameterZero)
  let l := Q.isLocalDiffeomorph_ambientNativeInteriorReferenceMap hdim (e parameterZero) u
  let ri : ℝ × IntrinsicInterior.Point k M → IntrinsicInterior.Point k M :=
    fun p => ⟨(R p.1).symm p.2.val,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((R p.1).symm.isLocalDiffeomorph p.2.val)).mp p.2.property⟩
  have hri : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1)))
      𝓘(ℝ, Model (k + 1)) ∞ ri := by
    apply IntrinsicInterior.contMDiff_iff_val.mpr
    exact hR.2.comp (contMDiff_id.prodMap IntrinsicInterior.contMDiff_val)
  let U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point) :=
    Prod.snd ⁻¹' l.localInverse.source
  have hU : IsOpen U := l.localInverse.open_source.preimage continuous_snd
  let g := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point =>
    ri (z.1, l.localInverse z.2)
  have hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      𝓘(ℝ, Model (k + 1)) ∞ g U := by
    apply hri.comp_contMDiffOn
    exact contMDiffOn_fst.prodMk
      (l.localInverse_contMDiffOn.comp contMDiffOn_snd (fun _ hz => hz))
  refine ⟨U, hU, l.localInverse_mem_source, g, hg, ?_, ?_⟩
  · change (R t.val).symm (l.localInverse (f u)).val = (R t.val).symm u.val
    rw [l.localInverse_left_inv l.localInverse_mem_target]
  · intro s y hy
    apply A.injective
    rw [A.apply_symm_apply]
    apply Prod.ext
    · rfl
    · change y = q (original (totalCollar (fun t p => C t p.val))
        (s, (R s.val).symm (l.localInverse y).val))
      rw [hqnative, Q.ambientNativeReferenceMap_eq_compact e R hsquareA]
      change y = Q.source.ambientCompletion.inclusion.map
        (e parameterZero (R s.val ((R s.val).symm (l.localInverse y).val))).val
      rw [(R s.val).apply_symm_apply]
      exact (l.localInverse_right_inv hy).symm

end FsFltz.Geometry.PairDeformation
