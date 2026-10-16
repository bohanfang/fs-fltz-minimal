import FsFltz.Geometry.IntrinsicNativeCompletionEndCanonicalChart
import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas

/-!
# The original interval-cylinder canonical-square bundle

Source: `geoemtric-part-fsf.tex`, smooth extension convention, lines 119–122;
`def:maslov`, lines 212–232; and `sec:lean`, lines 788–814. The base is the
original full cylinder patch of the completed total family, with its original
parameter in `[0,1]`. Fibers use the native completion tangent, normalized by
one fixed real basis equivalence. Local coframes are constructed from local
extensions of the original complex endomorphism, before any section is given.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology TensorProduct
open Set Filter Topology Bundle

namespace FsFltz.Geometry.IntrinsicCompletionGluing

variable {k n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]
  {δ : ℝ} (hδ : 0 < δ)
  (C : Parameter → ℝ × IntrinsicBoundary.Point k M → M)
  (hemb : ∀ t, IsOpenEmbedding (fun p : Half δ (IntrinsicBoundary.Point k M) => C t p.val))
  (hboundary : ∀ t (p : Half δ (IntrinsicBoundary.Point k M)),
    (𝓡∂ (k + 1)).IsBoundaryPoint (C t p.val) ↔ p.val.1 = 0)
  (hzero : ∀ t b, C t (0, b) = b.val)
  (J : ∀ s : Parameter, Space (fun p : Half δ (IntrinsicBoundary.Point k M) => C s p.val) →
    Model (k + 1) →L[ℝ] Model (k + 1))
  (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
  (P : Model (2 * n) ≃L[ℝ] (Model k × ℝ))

local instance : ChartedSpace (Model (k + 1)) (Band δ (IntrinsicBoundary.Point k M)) := bandChartedSpace δ
local instance : ChartedSpace (Model k × ℝ) (IntrinsicBoundary.Point k M × ℝ) :=
  prodChartedSpace (Model k) (IntrinsicBoundary.Point k M) ℝ ℝ
local instance : IsManifold 𝓘(ℝ, Model k × ℝ) ∞ (IntrinsicBoundary.Point k M × ℝ) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Model k)) (I' := 𝓘(ℝ, ℝ)) (IntrinsicBoundary.Point k M) ℝ

/-- The full original band in boundary–outward-radius coordinates. -/
def originalEndChartBandTarget (a : IntrinsicBoundary.Point k M × ℝ) : Set (Model k × ℝ) :=
  (chartAt (Model k × ℝ) a).target ∩
    (chartAt (Model k × ℝ) a).symm ⁻¹' {w | -w.2 < δ}

theorem isOpen_originalEndChartBandTarget (a : IntrinsicBoundary.Point k M × ℝ) :
    IsOpen (originalEndChartBandTarget (δ := δ) a) :=
  (chartAt (Model k × ℝ) a).continuousOn_symm.isOpen_inter_preimage
    (chartAt (Model k × ℝ) a).open_target (isOpen_lt continuous_snd.neg continuous_const)

/-- The actual original completion complex field over its full cylinder patch. -/
def originalEndComplex (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    Model (2 * n) →L[ℝ] Model (2 * n) :=
  N.symm.toContinuousLinearMap.comp
    ((J p.1 (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2)).comp
      N.toContinuousLinearMap)

/-- Coordinate expression of the original endomorphism, with its actual
completion inclusion and spatial chart differentials. -/
def originalEndComplexInChart (a : IntrinsicBoundary.Point k M × ℝ)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) : (Model k × ℝ) →L[ℝ] (Model k × ℝ) :=
  let H := originalEndCanonicalDifferential hδ (C p.1) (hemb p.1)
    (hboundary p.1) (hzero p.1) a p.2
  H.comp ((J p.1
    (cylinder (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2)).comp H.inverse)

/-- Source smoothness at interval endpoints means local open extensions of
the endomorphism in the original cylindrical-end charts, not whole-time complex laws. -/
def HasOriginalEndComplexExtensions : Prop :=
  ∀ (t : Parameter) (p : Band δ (IntrinsicBoundary.Point k M)),
    let a := endBandCoordinates p;
    ∃ (U : TopologicalSpace.Opens (ℝ × (Model k × ℝ)))
      (K : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] (Model k × ℝ)),
      (t.val, chartAt (Model k × ℝ) a a) ∈ U ∧ ContDiffOn ℝ ∞ K U ∧
      ∀ (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M)),
        endBandCoordinates w ∈ (chartAt (Model k × ℝ) a).source →
        (s.val, chartAt (Model k × ℝ) a (endBandCoordinates w)) ∈ U →
        K (s.val, chartAt (Model k × ℝ) a (endBandCoordinates w)) =
          originalEndComplexInChart hδ C hemb hboundary hzero J a (s, w)

/-- A canonical coframe chart on the original interval-cylinder. The open
extension is only a coframe; its canonical law is imposed solely at original
time values and uses the literal original complex field. -/
structure OriginalEndCanonicalChart where
  anchor : IntrinsicBoundary.Point k M × ℝ
  domain : TopologicalSpace.Opens (ℝ × (Model k × ℝ))
  subset_target : (domain : Set (ℝ × (Model k × ℝ))) ⊆
    univ ×ˢ originalEndChartBandTarget (δ := δ) anchor
  coframe : (ℝ × (Model k × ℝ)) → (Model k × ℝ) →L[ℝ] TangentCoordinates n
  smooth_coframe : ContDiffOn ℝ ∞ coframe domain
  invertible_coframe : ∀ z ∈ domain, (coframe z).IsInvertible
  intertwines : ∀ (s : Parameter) (w : Band δ (IntrinsicBoundary.Point k M)),
    endBandCoordinates w ∈ (chartAt (Model k × ℝ) anchor).source →
    (s.val, chartAt (Model k × ℝ) anchor (endBandCoordinates w)) ∈ domain → ∀ v,
    coframe (s.val, chartAt (Model k × ℝ) anchor (endBandCoordinates w))
      (originalEndComplexInChart hδ C hemb hboundary hzero J anchor (s, w) v) =
    coordinateComplexStructure n (coframe (s.val, chartAt (Model k × ℝ) anchor (endBandCoordinates w)) v)

variable
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

include P hC hinv in
theorem exists_originalEndCanonicalChart
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    ∃ c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n),
      c.anchor = endBandCoordinates p.2 ∧ (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2)) ∈ c.domain := by
  obtain ⟨U, K, hpU, hK, heK⟩ := hJ p.1 p.2
  let a := endBandCoordinates p.2
  let e := chartAt (Model k × ℝ) a
  let V : Set (ℝ × (Model k × ℝ)) := (U : Set _) ∩ (univ ×ˢ originalEndChartBandTarget (δ := δ) a)
  have hV : IsOpen V := U.isOpen.inter (isOpen_univ.prod (isOpen_originalEndChartBandTarget a))
  have hpV : (p.1.val, e a) ∈ V := by
    refine ⟨hpU, mem_univ _, e.map_source (mem_chart_source _ a), ?_⟩
    change -(e.symm (e a)).2 < δ
    rw [e.left_inv (mem_chart_source _ a)]
    change -(-p.2.val.1) < δ
    simpa only [neg_neg] using (show p.2.val.1 < δ from p.2.property.1)
  have hsq : ∀ z ∈ V ∩ (parameterInterval ×ˢ (univ : Set ((Model k × ℝ)))),
      ∀ v, K z (K z v) = -v := by
    intro z hz v
    let t : Parameter := ⟨z.1, hz.2.1⟩
    let w := e.symm z.2
    let q : Band δ (IntrinsicBoundary.Point k M) := ⟨(-w.2, w.1), hz.1.2.2.2, mem_univ _⟩
    have hqw : endBandCoordinates q = w := by simp only [endBandCoordinates, q, neg_neg, Prod.mk.eta]
    have hw : endBandCoordinates q ∈ e.source := hqw ▸ e.map_target hz.1.2.2.1
    have hew : chartAt (Model k × ℝ) a (endBandCoordinates q) = z.2 := by
      rw [hqw]; exact e.right_inv hz.1.2.2.1
    have hmatch := heK t q hw (by
      change (t.val, chartAt (Model k × ℝ) a (endBandCoordinates q)) ∈ U.carrier
      rw [hew]
      exact hz.1.1)
    have hmatch' : K z = originalEndComplexInChart hδ C hemb hboundary hzero J a (t, q) := by
      change K (z.1, chartAt (Model k × ℝ) a (endBandCoordinates q)) = _ at hmatch
      rw [hew] at hmatch
      exact hmatch
    rw [hmatch']
    let H := originalEndCanonicalDifferential hδ (C t) (hemb t) (hboundary t) (hzero t) a q
    have hHi : H.IsInvertible := isInvertible_originalEndCanonicalDifferential
      hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) a q hw
    change H (J t _ (H.inverse (H (J t _ (H.inverse v))))) = -v
    rw [hHi.inverse_apply_self, hJsq, map_neg, hHi.self_apply_inverse]
  obtain ⟨b, hbV, hpb⟩ := exists_nativeCoordinateCanonicalPatch P hV hpV
    (show (p.1.val, e a) ∈ parameterInterval ×ˢ (univ : Set ((Model k × ℝ))) from
      ⟨p.1.property, mem_univ _⟩) (hK.mono inter_subset_left) hsq
  refine ⟨{
    anchor := a
    domain := b.domain
    subset_target := fun _ hz => (hbV hz).2
    coframe := b.coframe
    smooth_coframe := b.smooth_coframe
    invertible_coframe := b.invertible_coframe
    intertwines := ?_ }, rfl, hpb⟩
  intro s w hw hwb v
  rw [← heK s w hw (hbV hwb).1]
  exact b.intertwines _ ⟨hwb, s.property, mem_univ _⟩ v

/-- The original complex field alone selects an cylindrical-end canonical cover. -/
def originalEndCanonicalChartAt
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :=
  (exists_originalEndCanonicalChart hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).choose


namespace OriginalEndCanonicalChart

variable (c : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
variable {hδ C hemb hboundary hzero J}

/-- This is the existing total family's full cylinder patch base. -/
def baseDomain : Set (Parameter × Band δ (IntrinsicBoundary.Point k M)) :=
  (univ ×ˢ (endBandCoordinates ⁻¹' (chartAt (Model k × ℝ) c.anchor).source)) ∩
    (fun p => (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2))) ⁻¹' c.domain

/-- All canonical slots are spatial. The original inclusion derivative is
part of the coframe, and is never an independently supplied map. -/
def nativeCoframe (N : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    Model (2 * n) →L[ℝ] TangentCoordinates n :=
  ((c.coframe (p.1.val, chartAt (Model k × ℝ) c.anchor (endBandCoordinates p.2))).comp
    (originalEndCanonicalDifferential hδ (C p.1) (hemb p.1)
      (hboundary p.1) (hzero p.1) c.anchor p.2)).comp N.toContinuousLinearMap

theorem isOpen_baseDomain : IsOpen c.baseDomain := by
  let e := chartAt (Model k × ℝ) c.anchor
  have hband := (contMDiff_endBandCoordinates (k := k) (M := M) (δ := δ)).continuous
  have hc : ContinuousOn (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
      (p.1.val, e (endBandCoordinates p.2))) (univ ×ˢ (endBandCoordinates ⁻¹' e.source)) :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      (e.continuousOn.comp (hband.comp continuous_snd).continuousOn (fun _ hp => hp.2))
  exact hc.isOpen_inter_preimage (isOpen_univ.prod (e.open_source.preimage hband)) c.domain.isOpen

include hC hinv in
theorem invertible_nativeCoframe {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hp : p ∈ c.baseDomain) : (c.nativeCoframe N p).IsInvertible :=
  ((c.invertible_coframe _ hp.2).comp
    (isInvertible_originalEndCanonicalDifferential hδ (C p.1) (hemb p.1) (hC p.1)
      (hboundary p.1) (hinv p.1) (hzero p.1) c.anchor p.2 hp.1.2)).comp ⟨N, rfl⟩

include hC hinv in
theorem nativeCoframe_intertwines {p : Parameter × Band δ (IntrinsicBoundary.Point k M)}
    (hp : p ∈ c.baseDomain) (v : Model (2 * n)) :
    c.nativeCoframe N p (originalEndComplex C J N p v) =
      coordinateComplexStructure n (c.nativeCoframe N p v) := by
  let H := originalEndCanonicalDifferential hδ (C p.1) (hemb p.1)
    (hboundary p.1) (hzero p.1) c.anchor p.2
  have hHi : H.IsInvertible := isInvertible_originalEndCanonicalDifferential
    hδ (C p.1) (hemb p.1) (hC p.1) (hboundary p.1) (hinv p.1) (hzero p.1)
    c.anchor p.2 hp.1.2
  have h := c.intertwines p.1 p.2 hp.1.2 hp.2 (H (N v))
  dsimp only [originalEndComplexInChart, ContinuousLinearMap.comp_apply] at h
  rw [hHi.inverse_apply_self] at h
  simpa only [nativeCoframe, originalEndComplex, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h


variable {N}

def lineCoordinateLinearMap (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) : canonicalSubmodule (originalEndComplex C J N x) →ₗ[ℂ] ℂ where
  toFun s := canonicalCoframeCoefficient (c.nativeCoframe N x) s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineCoordinateEquiv (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hx : x ∈ c.baseDomain) :
    canonicalSubmodule (originalEndComplex C J N x) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.lineCoordinateLinearMap (N := N) x
  invFun q := q • (⟨coframeCanonicalGenerator (c.nativeCoframe N x),
    coframeCanonicalGenerator_canonical _ (c.invertible_nativeCoframe (N := N) hC hinv hx) _
      (c.nativeCoframe_intertwines (N := N) hC hinv hx)⟩ : canonicalSubmodule (originalEndComplex C J N x))
  left_inv s := Subtype.ext (canonicalCoframe_reconstruction _
    (c.invertible_nativeCoframe (N := N) hC hinv hx) _ (c.nativeCoframe_intertwines (N := N) hC hinv hx) _ s.property).symm
  right_inv q := by
    change q * canonicalCoframeCoefficient (c.nativeCoframe N x)
      (coframeCanonicalGenerator (c.nativeCoframe N x)) = q
    rw [coframeCanonicalGenerator_frame _ (c.invertible_nativeCoframe (N := N) hC hinv hx), mul_one]

/-- The coordinate is the tensor product of two unsquared line
coordinates, independently of natural square multiplication. -/
def tensorCoordinateLinearMap (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) : CanonicalTensorSquare (originalEndComplex C J N x) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (c.lineCoordinateLinearMap (N := N) x) (c.lineCoordinateLinearMap (N := N) x))

def tensorCoordinateEquiv (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hx : x ∈ c.baseDomain) :
    CanonicalTensorSquare (originalEndComplex C J N x) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (c.lineCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx) (c.lineCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx)).trans
    (TensorProduct.lid ℂ ℂ)

@[simp] theorem tensorCoordinateEquiv_toLinearMap (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hx : x ∈ c.baseDomain) :
    (c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx).toLinearMap = c.tensorCoordinateLinearMap (N := N) x := rfl

def tensorCoordinateContinuousEquiv (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) (hx : x ∈ c.baseDomain) :
    CanonicalTensorSquare (originalEndComplex C J N x) ≃L[ℂ] ℂ where
  toLinearEquiv := c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx).symm.toLinearMap
    exact IsModuleTopology.continuous_of_linearMap _

/-- The bridge is an equality of the independently constructed scalar
coordinates, proved on pure tensors and extended by tensor linearity. -/
theorem coefficient_squareMap (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) (t : CanonicalTensorSquare (originalEndComplex C J N x)) :
    squaredCoframeCoefficient (c.nativeCoframe N x) (canonicalSquareMap (originalEndComplex C J N x) t).val =
      c.tensorCoordinateLinearMap (N := N) x t := by
  let L : squaredCanonicalSubmodule (originalEndComplex C J N x) →ₗ[ℂ] ℂ :=
    { toFun s := squaredCoframeCoefficient (c.nativeCoframe N x) s.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : L.comp (canonicalSquareMap (originalEndComplex C J N x)) = c.tensorCoordinateLinearMap (N := N) x := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro u
    change squaredCoframeCoefficient (c.nativeCoframe N x)
      (canonicalSquareMap (originalEndComplex C J N x) (s ⊗ₜ[ℂ] u)).val =
      canonicalCoframeCoefficient (c.nativeCoframe N x) s.val *
        canonicalCoframeCoefficient (c.nativeCoframe N x) u.val
    rw [canonicalSquareMap_tmul]
    simp only [squaredCoframeCoefficient, canonicalTensorProduct_apply,
      canonicalCoframeCoefficient, Sum.elim_inl, Sum.elim_inr, id_eq]
  exact congrArg (fun f => f t) h

open scoped Classical in
def tensorPretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : (Parameter × Band δ (IntrinsicBoundary.Point k M)) => CanonicalTensorSquare (originalEndComplex C J N x))) where
  toFun p := (p.proj, c.tensorCoordinateLinearMap (N := N) p.proj p.snd)
  invFun p := if hp : p.1 ∈ c.baseDomain then
    ⟨p.1, (c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : (Parameter × Band δ (IntrinsicBoundary.Point k M)) => CanonicalTensorSquare (originalEndComplex C J N x))) ⁻¹' c.baseDomain
  target := c.baseDomain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.baseDomain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : CanonicalTensorSquare (originalEndComplex C J N x) =>
      (⟨x, t⟩ : Bundle.TotalSpace ℂ (fun x => CanonicalTensorSquare (originalEndComplex C J N x))))
      ((c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hp).symm_apply_apply s)
  right_inv' p hp := by
    rw [dite_eq_left hp.1]
    exact Prod.ext rfl ((c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) p.1 hp.1).apply_symm_apply p.2)
  open_target := c.isOpen_baseDomain.prod isOpen_univ
  baseSet := c.baseDomain
  open_baseSet := c.isOpen_baseDomain
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance tensorPretrivialization_complexLinear : c.tensorPretrivialization (N := N) (hC := hC) (hinv := hinv).IsLinear ℂ where
  linear x _ := (c.tensorCoordinateLinearMap (N := N) x).isLinear

instance tensorPretrivialization_realLinear : c.tensorPretrivialization (N := N) (hC := hC) (hinv := hinv).IsLinear ℝ where
  linear x _ := ((c.tensorCoordinateLinearMap (N := N) x).restrictScalars ℝ).isLinear

theorem tensorPretrivialization_symm {x : (Parameter × Band δ (IntrinsicBoundary.Point k M))} (hx : x ∈ c.baseDomain) (q : ℂ) :
    c.tensorPretrivialization (N := N) (hC := hC) (hinv := hinv).symm x q = (c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx).symm q := by
  apply (c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx).injective
  rw [(c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.tensorPretrivialization (N := N) (hC := hC) (hinv := hinv).apply_mk_symm hx q)

theorem tensorPretrivialization_isInducing {x : (Parameter × Band δ (IntrinsicBoundary.Point k M))} (hx : x ∈ c.baseDomain) :
    Topology.IsInducing (c.tensorPretrivialization (N := N) (hC := hC) (hinv := hinv) ∘ Bundle.TotalSpace.mk x) := by
  have h := (c.tensorCoordinateContinuousEquiv (N := N) (hC := hC) (hinv := hinv) x hx).toHomeomorph.isInducing
  change Topology.IsInducing (c.tensorCoordinateEquiv (N := N) (hC := hC) (hinv := hinv) x hx).toLinearMap at h
  rw [c.tensorCoordinateEquiv_toLinearMap] at h
  have hlin : Continuous (c.tensorCoordinateLinearMap (N := N) x) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (c.tensorPretrivialization (N := N) (hC := hC) (hinv := hinv) ∘ Bundle.TotalSpace.mk x) :=
    continuous_const.prodMk hlin
  exact Topology.IsInducing.of_comp hc continuous_snd h

include hC hinv in
theorem reconstruction {x : Parameter × Band δ (IntrinsicBoundary.Point k M)} (hx : x ∈ c.baseDomain)
    (s : squaredCanonicalSubmodule (originalEndComplex C J N x)) :
    s.val = squaredCoframeCoefficient (c.nativeCoframe N x) s.val •
      coframeSquaredGenerator (c.nativeCoframe N x) :=
  squaredCoframe_reconstruction _ (c.invertible_nativeCoframe (N := N) hC hinv hx) _
    (c.nativeCoframe_intertwines (N := N) hC hinv hx) _ s.property

def transition (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) : ℂ :=
  squaredCoframeTransition (c.nativeCoframe N x) (d.nativeCoframe N x)

theorem tensorTransition_apply
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : Parameter × Band δ (IntrinsicBoundary.Point k M)} (hx : x ∈ c.baseDomain ∩ d.baseDomain) (q : ℂ) :
    (d.tensorPretrivialization (N := N) hC hinv
      ⟨x, (c.tensorPretrivialization (N := N) hC hinv).symm x q⟩).2 =
      c.transition (N := N) d x * q := by
  rw [c.tensorPretrivialization_symm hC hinv hx.1]
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv hC hinv x hx.1).symm q) = _
  rw [← d.coefficient_squareMap]
  have hr := c.reconstruction hC hinv hx.1
    (canonicalSquareMap (originalEndComplex C J N x) ((c.tensorCoordinateEquiv hC hinv x hx.1).symm q))
  have hq : squaredCoframeCoefficient (c.nativeCoframe N x)
      (canonicalSquareMap (originalEndComplex C J N x) ((c.tensorCoordinateEquiv hC hinv x hx.1).symm q)).val = q := by
    rw [c.coefficient_squareMap]
    exact (c.tensorCoordinateEquiv hC hinv x hx.1).apply_symm_apply q
  rw [hq] at hr
  rw [hr]
  change q * squaredCoframeCoefficient (d.nativeCoframe N x)
    (coframeSquaredGenerator (c.nativeCoframe N x)) = _
  exact mul_comm _ _


/-- The overlap in the denominator chart's genuine real coordinates. -/
def transitionDomain
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Set (ℝ × (Model k × ℝ)) :=
  (univ ×ˢ originalEndCoordinateOverlap d.anchor c.anchor) ∩
    (fun p => (p.1, chartAt (Model k × ℝ) c.anchor
      ((chartAt (Model k × ℝ) d.anchor).symm p.2))) ⁻¹' c.domain ∩ d.domain

def transitionExtension
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : ℝ × (Model k × ℝ)) : ℂ :=
  squaredCoframeTransition
    (((c.coframe (p.1, chartAt (Model k × ℝ) c.anchor
      ((chartAt (Model k × ℝ) d.anchor).symm p.2))).comp
      (fderiv ℝ ((chartAt (Model k × ℝ) c.anchor) ∘
        (chartAt (Model k × ℝ) d.anchor).symm) p.2)).comp P.toContinuousLinearMap)
    ((d.coframe p).comp P.toContinuousLinearMap)

theorem smooth_transitionExtension
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContDiffOn ℝ ∞ (c.transitionExtension (P := P) d) (c.transitionDomain d) :=
  contDiffOn_originalEndSquaredTransition P d.anchor c.anchor
    (d.smooth_coframe.mono inter_subset_right) c.smooth_coframe
    (fun _ hp => hp.1.1) (fun _ hp => hp.1.2)
    (fun _ hp => d.invertible_coframe _ hp.2)

include P hC hinv in
theorem smooth_transition
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (c.transition (N := N) d) (c.baseDomain ∩ d.baseDomain) := by
  let e := chartAt (Model k × ℝ) d.anchor
  let z := fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
    (p.1.val, e (endBandCoordinates p.2))
  have ht : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => p.1.val) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hband : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => endBandCoordinates p.2) :=
    contMDiff_endBandCoordinates.comp contMDiff_snd
  have hx : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, Model k × ℝ) ∞
      (fun p : Parameter × Band δ (IntrinsicBoundary.Point k M) => e (endBandCoordinates p.2))
      (c.baseDomain ∩ d.baseDomain) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model k × ℝ)) (x := d.anchor)).comp
      hband.contMDiffOn (fun _ hp => hp.2.1.2)
  have hz : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℝ × (Model k × ℝ)) ∞ z
      (c.baseDomain ∩ d.baseDomain) := ht.contMDiffOn.prodMk_space hx
  have hzD : MapsTo z (c.baseDomain ∩ d.baseDomain) (c.transitionDomain d) := by
    intro p hp
    refine ⟨⟨⟨mem_univ _, e.map_source hp.2.1.2, ?_⟩, ?_⟩, hp.2.2⟩
    · change e.symm (e (endBandCoordinates p.2)) ∈ (chartAt (Model k × ℝ) c.anchor).source
      rw [e.left_inv hp.2.1.2]
      exact hp.1.1.2
    · change (p.1.val, chartAt (Model k × ℝ) c.anchor (e.symm (e (endBandCoordinates p.2)))) ∈ c.domain
      rw [e.left_inv hp.2.1.2]
      exact hp.1.2
  apply ((c.smooth_transitionExtension (P := P) d).contMDiffOn.comp hz hzD).congr
  intro p hp
  change c.transition (N := N) d p = c.transitionExtension (P := P) d (z p)
  dsimp only [transition, nativeCoframe, transitionExtension, z]
  rw [e.left_inv hp.2.1.2]
  exact originalEndCanonical_squaredTransition hδ (C p.1) (hemb p.1) (hC p.1)
    (hboundary p.1) (hinv p.1) (hzero p.1) N P d.anchor c.anchor p.2
    hp.2.1.2 hp.1.1.2 _ _


def transitionMap
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) : ℂ →L[ℝ] ℂ :=
  c.transition (N := N) d x • ContinuousLinearMap.id ℝ ℂ

include P hC hinv in
theorem smooth_transitionMap
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.transitionMap (N := N) d) (c.baseDomain ∩ d.baseDomain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_transition (N := N) (P := P) hC hinv d)

theorem transitionMap_apply
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : Parameter × Band δ (IntrinsicBoundary.Point k M)} (hx : x ∈ c.baseDomain ∩ d.baseDomain) (q : ℂ) :
    c.transitionMap (N := N) d x q =
      (d.tensorPretrivialization (N := N) hC hinv
        ⟨x, (c.tensorPretrivialization (N := N) hC hinv).symm x q⟩).2 :=
  (c.tensorTransition_apply hC hinv d hx q).symm

theorem isOpen_transitionDomain
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    IsOpen (c.transitionDomain d) := by
  have hg := (contDiffOn_originalEndCoordinateTransition d.anchor c.anchor).continuousOn
  have hm : ContinuousOn (fun p : ℝ × (Model k × ℝ) =>
      (p.1, chartAt (Model k × ℝ) c.anchor ((chartAt (Model k × ℝ) d.anchor).symm p.2)))
      (univ ×ˢ originalEndCoordinateOverlap d.anchor c.anchor) :=
    continuous_fst.continuousOn.prodMk
      (hg.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  exact (hm.isOpen_inter_preimage
    (isOpen_univ.prod (isOpen_originalEndCoordinateOverlap d.anchor c.anchor))
    c.domain.isOpen).inter d.domain.isOpen

include hC hinv in
/-- All original coframe charts give coordinates on the same native fiber. -/
theorem tensorCoordinateLinearMap_transition
    (d : OriginalEndCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : Parameter × Band δ (IntrinsicBoundary.Point k M)} (hx : x ∈ c.baseDomain ∩ d.baseDomain)
    (τ : CanonicalTensorSquare (originalEndComplex C J N x)) :
    d.tensorCoordinateLinearMap x τ = c.transition (N := N) d x * c.tensorCoordinateLinearMap x τ := by
  have h := c.tensorTransition_apply (N := N) hC hinv d hx (c.tensorCoordinateLinearMap x τ)
  rw [c.tensorPretrivialization_symm hC hinv hx.1] at h
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv hC hinv x hx.1).symm
    ((c.tensorCoordinateEquiv hC hinv x hx.1) τ)) = _ at h
  rwa [(c.tensorCoordinateEquiv hC hinv x hx.1).symm_apply_apply] at h


end OriginalEndCanonicalChart
/-- The cover includes every point of the original interval-full cylinder patch. -/
theorem mem_originalEndCanonicalChartAt
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (p : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    p ∈ (originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).baseDomain := by
  have h := (exists_originalEndCanonicalChart hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).choose_spec
  refine ⟨⟨mem_univ _, ?_⟩, h.2⟩
  rw [show (originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).anchor = endBandCoordinates p.2 from h.1]
  exact mem_chart_source (Model k × ℝ) (endBandCoordinates p.2)

/-- The actual interval-cylinder tensor-square prebundle. Its atlas consists
of all the original canonical coframe charts, independently of a section or
any encoded Maslov family. -/
def originalEndCanonicalTensorSquareVectorPrebundle
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : Parameter × Band δ (IntrinsicBoundary.Point k M) =>
      CanonicalTensorSquare (originalEndComplex C J N x)) where
  pretrivializationAtlas := Set.range
    (OriginalEndCanonicalChart.tensorPretrivialization (N := N) hC hinv)
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt p :=
    (originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).tensorPretrivialization hC hinv
  mem_base_pretrivializationAt :=
    mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq
  pretrivialization_mem_atlas p := ⟨_, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap (N := N) d, (c.smooth_transitionMap (P := P) hC hinv d).continuousOn,
      fun _ hx q => c.transitionMap_apply hC hinv d hx q⟩
  totalSpaceMk_isInducing p :=
    (originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).tensorPretrivialization_isInducing hC hinv
      (mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p)

instance originalEndCanonicalTensorSquareVectorPrebundle_isContMDiff
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    (originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq).IsContMDiff
      (familyModel (k + 1)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap (N := N) d, c.smooth_transitionMap (P := P) hC hinv d,
      fun _ hx q => c.transitionMap_apply hC hinv d hx q⟩

/-- The constructed original interval-cylinder bundle is smoothly locally
trivial, including both parameter endpoints. -/
theorem originalEndCanonicalTensorSquareVectorBundle_smooth
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    let a := originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ
      (fun x : Parameter × Band δ (IntrinsicBoundary.Point k M) => CanonicalTensorSquare (originalEndComplex C J N x))
      (familyModel (k + 1)) :=
  (originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq).contMDiffVectorBundle _

/-- The same atlas has complex-linear transitions and defines a complex
line bundle on the original cylindrical-end base. -/
theorem originalEndCanonicalTensorSquareVectorBundle_complex
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    let a := originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ
      (fun x : Parameter × Band δ (IntrinsicBoundary.Point k M) => CanonicalTensorSquare (originalEndComplex C J N x)) := by
  dsimp only
  let a := originalEndCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J N P hC hinv hJ hJsq
  let := a.totalSpaceTopology
  let := a.toFiberBundle
  refine ⟨?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨c, rfl⟩ := he
    exact ⟨fun x _ => (c.tensorCoordinateLinearMap x).isLinear⟩
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    obtain ⟨c, rfl⟩ := he
    obtain ⟨d, rfl⟩ := he'
    let L : ℂ →L[ℂ] (ℂ →L[ℂ] ℂ) :=
      ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℂ ℂ)
    have hc : ContinuousOn (fun x => L (c.transition (N := N) d x)) (c.baseDomain ∩ d.baseDomain) :=
      L.continuous.comp_continuousOn (c.smooth_transition (P := P) hC hinv d).continuousOn
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (c.transitionMap_apply hC hinv d hx q).symm
    · exact hx


include P hC hinv in
/-- Every original canonical-square fiber is a complex line. -/
theorem originalEndCanonicalTensorSquare_finrank
    (hJ : HasOriginalEndComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (x : Parameter × Band δ (IntrinsicBoundary.Point k M)) :
    Module.finrank ℂ (CanonicalTensorSquare (originalEndComplex C J N x)) = 1 := by
  let c := originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  have hx : x ∈ c.baseDomain :=
    mem_originalEndCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  rw [(c.tensorCoordinateEquiv (N := N) hC hinv x hx).finrank_eq]
  exact Module.finrank_self ℂ


end FsFltz.Geometry.IntrinsicCompletionGluing
