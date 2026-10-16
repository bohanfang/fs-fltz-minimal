import FsFltz.Geometry.IntrinsicNativeCompletionFamilyInverseGerms

/-!
# Descent of local real coefficient extensions through the original inverse

Source: `geoemtric-part-fsf.tex`, `def:maslov`, lines 212–244, and
`sec:lean`, lines 788–814. Local coefficients on the original interior and
completion cylinder give genuine real-open extensions after the original
total comparison inverse. All interval values, including both endpoints,
are retained. This is the coefficient composition step; tangent-coframe
transport and the grading constructors are separate consumers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter Topology

namespace FsFltz.Geometry

/-- The spatial differential of a parameter-preserving real inverse germ
is invertible. The proof restricts the actual full derivative to the vertical
subspace; the time component is fixed, including at interval endpoints. -/
theorem isInvertible_verticalDerivative_of_parameterPartialDiffeomorph
    {E F P N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace P] [ChartedSpace E P]
    [TopologicalSpace N] [ChartedSpace F N]
    (l : PartialDiffeomorph ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) (ℝ × P) (ℝ × N) ∞)
    (g : ℝ × P → N) {U : Set (ℝ × P)} (hU : IsOpen U)
    (hUl : U ⊆ l.source) (he : ∀ z ∈ U, l z = (z.1, g z))
    (hg : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ g U)
    {p : ℝ × P} (hp : p ∈ U) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => g (p.1, x)) p.2).IsInvertible := by
  let H := fun z : ℝ × P => (z.1, g z)
  have hgd := (hg.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  have heq : H =ᶠ[𝓝 p] l := by
    filter_upwards [hU.mem_nhds hp] with z hz
    exact (he z hz).symm
  have hDbij : Function.Bijective (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) H p) := by
    rw [heq.mfderiv_eq]
    exact (tangentSpaceCast ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) (l p) (H p)).bijective.comp
      ((l.isLocalDiffeomorphAt _ _ _ (hUl hp)).isInvertible_mfderiv (by simp)).bijective
  let B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (fun x => g (p.1, x)) p.2
  have hB : B = (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) g p).comp
      (ContinuousLinearMap.inr ℝ ℝ E) := by
    change mfderiv _ _ (g ∘ fun x => (p.1, x)) p.2 = _
    have h := mfderiv_comp (f := fun x : P => (p.1, x)) p.2 hgd
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    rw [mfderiv_prod_right] at h
    exact h
  have hD : mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, F)) H p =
        (ContinuousLinearMap.fst ℝ ℝ E).prod
          (mfderiv ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) g p) := by
    exact (mfderiv_prodMk mdifferentiableAt_fst hgd).trans (by rw [mfderiv_fst]; rfl)
  have hBij : Function.Bijective B := by
    constructor
    · intro v w hvw
      have hEq : ((0 : ℝ), v) = (0, w) := hDbij.1 (a₁ := (0, v)) (a₂ := (0, w)) (by
        rw [hD]
        rw [hB] at hvw
        exact Prod.ext rfl hvw)
      exact congrArg Prod.snd hEq
    · intro w
      obtain ⟨⟨u, v⟩, hv⟩ := hDbij.2 (0, w)
      rw [hD] at hv
      have hu : u = 0 := congrArg Prod.fst hv
      subst u
      refine ⟨v, ?_⟩
      have hs := congrArg Prod.snd hv
      rw [hB]
      exact hs
  exact ⟨(LinearEquiv.ofBijective B.toLinearMap hBij).toContinuousLinearEquiv, rfl⟩

end FsFltz.Geometry

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
/-- The real end inverse of the original completed comparison has an
invertible spatial differential throughout its real-open neighborhood.
The same germ retains the actual original total inverse at all interval
points; invertibility is proved from its parameter-preserving partial
diffeomorphism, not assumed as additional grading data. -/
theorem exists_ambientNativeTotalEquiv_symm_realEndGerm_verticalDerivative
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ U ∧
      ∃ g : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → IntrinsicBoundary.Point k M × ℝ,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) ∞ g U ∧
        g (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) = (x, r) ∧
        (∀ z ∈ U, (mfderiv 𝓘(ℝ, Model (2 * n))
          ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)) (fun y => g (z.1, y)) z.2).IsInvertible) ∧
        (∀ z ∈ U, -(g z).2 < δ) ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          ∃ p : Band δ (IntrinsicBoundary.Point k M),
            p.val = (-(g (s.val, y)).2, (g (s.val, y)).1) ∧
            (Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y) =
              totalCylinder (fun t p => C t p.val) (s, p) := by
  obtain ⟨U, hU, hpU, g, hg, hgp, ⟨l, hUl, hl⟩, hband, heq⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_realEndGerm hdim α e hp hc b hb hsquareB
      R hsquareA hδ C hzero hode q hqnative hqend t x r hr
  refine ⟨U, hU, hpU, g, hg, hgp, ?_, hband, heq⟩
  intro z hz
  let : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
    prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
  have H := @isInvertible_verticalDerivative_of_parameterPartialDiffeomorph
    (Model (2 * n)) (Model k × ℝ)
    Q.source.ambientCompletion.ambient.manifold.Point (IntrinsicBoundary.Point k M × ℝ)
    _ _ _ _ _ _ _ _ _ _
  rw [modelWithCornersSelf_prod (E := Model k) (F := ℝ)] at H
  exact H l g hU hUl hl hg hz

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

include hdim α hp hc hb hsquareB hzero hode in
/-- A source-local coefficient extension near an actual native end point
descends through the real inverse germ of the original total comparison.
No smooth extension of the inverse on the whole real time axis is required. -/
theorem exists_ambientNativeTotalEquiv_symm_endCoefficientExtension
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → E)
    (t : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ) (hr : 0 ≤ r)
    (V : Set (ℝ × (IntrinsicBoundary.Point k M × ℝ))) (hV : IsOpen V)
    (hpV : (t.val, (x, r)) ∈ V)
    (a : ℝ × (IntrinsicBoundary.Point k M × ℝ) → E)
    (ha : ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
      𝓘(ℝ, E) ∞ a V)
    (haeq : ∀ (s : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
      (s.val, (p.val.2, -p.val.1)) ∈ V →
        a (s.val, (p.val.2, -p.val.1)) = f (totalCylinder (fun t p => C t p.val) (s, p))) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ U ∧
      ∃ a' : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → E,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, E) ∞ a' U ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          a' (s.val, y) = f
            ((Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y)) := by
  obtain ⟨U, hU, hpU, g, hg, hgp, _, _, heq⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_realEndGerm hdim α e hp hc b hb hsquareB
      R hsquareA hδ C hzero hode q hqnative hqend t x r hr
  let G := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point => (z.1, g z)
  have hG : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ))) ∞ G U :=
    contMDiffOn_fst.prodMk hg
  let W := U ∩ G ⁻¹' V
  have hW : IsOpen W := hG.continuousOn.isOpen_inter_preimage hU hV
  have hpW : (t.val, Q.source.ambientCompletion.endMap (b parameterZero x, r)) ∈ W := by
    refine ⟨hpU, ?_⟩
    change (t.val, g _) ∈ V
    rwa [hgp]
  refine ⟨W, hW, hpW, a ∘ G,
    ha.comp (hG.mono inter_subset_left) inter_subset_right, ?_⟩
  intro s y hy
  obtain ⟨p, hp, he⟩ := heq s y hy.1
  rw [he]
  have hp' : (p.val.2, -p.val.1) = g (s.val, y) := by
    rw [hp]
    simp only [neg_neg]
  simpa only [Function.comp_apply, G, hp'] using haeq s p (hp'.symm ▸ hy.2)

include hdim hR in
/-- Interior coefficients descend using the actual native inverse formula.
Source regularity is needed only near the corresponding native point. -/
theorem exists_ambientNativeTotalEquiv_symm_interiorCoefficientExtension
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → E)
    (hlocal : ∀ (s : Parameter) (v : IntrinsicInterior.Point k M),
      ∃ V : Set (ℝ × IntrinsicInterior.Point k M), IsOpen V ∧ (s.val, v) ∈ V ∧
        ∃ a : ℝ × IntrinsicInterior.Point k M → E,
          ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, E) ∞ a V ∧
          ∀ (u : Parameter) w, (u.val, w) ∈ V →
            a (u.val, w) = f (totalInterior (fun t p => C t p.val) (u, w)))
    (t : Parameter) (v : IntrinsicInterior.Point k M) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, Q.ambientNativeInteriorReferenceMap (e parameterZero) v) ∈ U ∧
      ∃ a' : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → E,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, E) ∞ a' U ∧
        ∀ (s : Parameter) y, (s.val, y) ∈ U →
          a' (s.val, y) = f
            ((Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, y)) := by
  obtain ⟨U, hU, hpU, g, hg, _, heq⟩ :=
    Q.exists_ambientNativeTotalEquiv_symm_realInteriorGerm hdim e b R hR hsquareA
      hδ C q hqnative hqend t v
  obtain ⟨V, hV, hpV, a, ha, hae⟩ :=
    hlocal t (g (t.val, Q.ambientNativeInteriorReferenceMap (e parameterZero) v))
  let G := fun z : ℝ × Q.source.ambientCompletion.ambient.manifold.Point => (z.1, g z)
  have hG : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n)))
      ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) ∞ G U := contMDiffOn_fst.prodMk hg
  let W := U ∩ G ⁻¹' V
  refine ⟨W, hG.continuousOn.isOpen_inter_preimage hU hV, ⟨hpU, hpV⟩,
    a ∘ G, ha.comp (hG.mono inter_subset_left) inter_subset_right, ?_⟩
  intro s y hy
  rw [heq s y hy.1]
  exact hae s (g (s.val, y)) hy.2

include hdim α hp hc hb hsquareB hzero hode hR in
/-- Local real coefficients on the original interior and cylinder cover
descend at every point of the reference completion, through the very same
total comparison inverse. The hypotheses are source-local and impose no
conditions outside their stated real-open neighborhoods. -/
theorem exists_ambientNativeTotalEquiv_symm_localCoefficientExtension
    (f : TotalSpace (fun t (p : Half δ (IntrinsicBoundary.Point k M)) => C t p.val) → E)
    (hinterior : ∀ (s : Parameter) (v : IntrinsicInterior.Point k M),
      ∃ V : Set (ℝ × IntrinsicInterior.Point k M), IsOpen V ∧ (s.val, v) ∈ V ∧
        ∃ a : ℝ × IntrinsicInterior.Point k M → E,
          ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (k + 1))) 𝓘(ℝ, E) ∞ a V ∧
          ∀ (u : Parameter) w, (u.val, w) ∈ V →
            a (u.val, w) = f (totalInterior (fun t p => C t p.val) (u, w)))
    (hend : ∀ (s : Parameter) (x : IntrinsicBoundary.Point k M) (r : ℝ), 0 ≤ r →
      ∃ V : Set (ℝ × (IntrinsicBoundary.Point k M × ℝ)),
        IsOpen V ∧ (s.val, (x, r)) ∈ V ∧
        ∃ a : ℝ × (IntrinsicBoundary.Point k M × ℝ) → E,
          ContMDiffOn ((𝓘(ℝ, ℝ)).prod ((𝓘(ℝ, Model k)).prod 𝓘(ℝ, ℝ)))
            𝓘(ℝ, E) ∞ a V ∧
          ∀ (u : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
            (u.val, (p.val.2, -p.val.1)) ∈ V →
              a (u.val, (p.val.2, -p.val.1)) =
                f (totalCylinder (fun t p => C t p.val) (u, p)))
    (t : Parameter) (y : Q.source.ambientCompletion.ambient.manifold.Point) :
    ∃ U : Set (ℝ × Q.source.ambientCompletion.ambient.manifold.Point),
      IsOpen U ∧ (t.val, y) ∈ U ∧
      ∃ a' : ℝ × Q.source.ambientCompletion.ambient.manifold.Point → E,
        ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model (2 * n))) 𝓘(ℝ, E) ∞ a' U ∧
        ∀ (s : Parameter) z, (s.val, z) ∈ U →
          a' (s.val, z) = f
            ((Q.ambientNativeTotalEquiv e b R hsquareA hδ C q hqnative hqend).symm (s, z)) := by
  let K := Q.source.ambientCompletion
  let D := Q.source.ambientDomain.domain
  by_cases hy : y ∈ K.inclusion.map '' interior D.carrier
  · obtain ⟨x, hx, rfl⟩ := hy
    let v : D.Point := ⟨x, interior_subset hx⟩
    have hv : (𝓡∂ (2 * n)).IsInteriorPoint v := by
      change v ∈ (𝓡∂ (2 * n)).interior D.Point
      rw [D.interior_eq_interior]
      exact hx
    let u : IntrinsicInterior.Point k M := ⟨(e parameterZero).symm v,
      (IsLocalDiffeomorphAt.isInteriorPoint_iff (by simp)
        ((e parameterZero).symm.isLocalDiffeomorph v)).mp hv⟩
    have h := Q.exists_ambientNativeTotalEquiv_symm_interiorCoefficientExtension
      hdim e b R hR hsquareA hδ C q hqnative hqend f hinterior t u
    simpa only [ambientNativeInteriorReferenceMap, u, v, K, source, Diffeomorph.apply_symm_apply] using h
  · have hyend : y ∈ range (fun p : D.boundary.Point × Ici (0 : ℝ) =>
        K.endMap (p.1, p.2)) := by
      rw [K.range_nonnegative_endMap]
      exact hy
    obtain ⟨⟨x, ⟨r, hr⟩⟩, rfl⟩ := hyend
    obtain ⟨V, hV, hpV, a, ha, he⟩ := hend t ((b parameterZero).symm x) r hr
    have h := Q.exists_ambientNativeTotalEquiv_symm_endCoefficientExtension
      hdim α e hp hc b hb hsquareB R hsquareA hδ C hzero hode q hqnative hqend
      f t ((b parameterZero).symm x) r hr V hV hpV a ha he
    simpa only [Diffeomorph.apply_symm_apply] using h

end FsFltz.Geometry.PairDeformation
