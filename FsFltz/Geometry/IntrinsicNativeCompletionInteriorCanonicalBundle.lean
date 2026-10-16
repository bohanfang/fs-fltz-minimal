import FsFltz.Geometry.IntrinsicNativeCompletionInteriorCanonicalChart
import FsFltz.Geometry.IntrinsicCompletionFamilyAtlas

/-!
# The original interval-interior canonical-square bundle

Source: `geoemtric-part-fsf.tex`, smooth extension convention, lines 119–122;
`def:maslov`, lines 212–232; and `sec:lean`, lines 788–814. The base is the
original interior patch of the completed total family, with its original
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
  (P : Model (2 * n) ≃L[ℝ] Model (k + 1))

/-- The actual original completion complex field over its interior patch. -/
def originalInteriorComplex (p : Parameter × IntrinsicInterior.Point k M) :
    Model (2 * n) →L[ℝ] Model (2 * n) :=
  P.symm.toContinuousLinearMap.comp
    ((J p.1 (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2)).comp
      P.toContinuousLinearMap)

/-- Coordinate expression of the original endomorphism, with its actual
completion inclusion and spatial chart differentials. -/
def originalInteriorComplexInChart (a : IntrinsicInterior.Point k M)
    (p : Parameter × IntrinsicInterior.Point k M) : Model (k + 1) →L[ℝ] Model (k + 1) :=
  let H := originalInteriorCanonicalDifferential hδ (C p.1) (hemb p.1)
    (hboundary p.1) (hzero p.1) a p.2
  H.comp ((J p.1
    (interiorIn (fun q : Half δ (IntrinsicBoundary.Point k M) => C p.1 q.val) p.2)).comp H.inverse)

/-- Source smoothness at interval endpoints means local open extensions of
the endomorphism in the original interior charts, not whole-time complex laws. -/
def HasOriginalInteriorComplexExtensions : Prop :=
  ∀ (t : Parameter) (a : IntrinsicInterior.Point k M),
    ∃ (U : TopologicalSpace.Opens (ℝ × Model (k + 1)))
      (K : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] Model (k + 1)),
      (t.val, chartAt (Model (k + 1)) a a) ∈ U ∧ ContDiffOn ℝ ∞ K U ∧
      ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
        w ∈ (chartAt (Model (k + 1)) a).source →
        (s.val, chartAt (Model (k + 1)) a w) ∈ U →
        K (s.val, chartAt (Model (k + 1)) a w) =
          originalInteriorComplexInChart hδ C hemb hboundary hzero J a (s, w)

/-- A canonical coframe chart on the original interval-interior. The open
extension is only a coframe; its canonical law is imposed solely at original
time values and uses the literal original complex field. -/
structure OriginalInteriorCanonicalChart where
  anchor : IntrinsicInterior.Point k M
  domain : TopologicalSpace.Opens (ℝ × Model (k + 1))
  subset_target : (domain : Set (ℝ × Model (k + 1))) ⊆
    univ ×ˢ (chartAt (Model (k + 1)) anchor).target
  coframe : (ℝ × Model (k + 1)) → Model (k + 1) →L[ℝ] TangentCoordinates n
  smooth_coframe : ContDiffOn ℝ ∞ coframe domain
  invertible_coframe : ∀ z ∈ domain, (coframe z).IsInvertible
  intertwines : ∀ (s : Parameter) (w : IntrinsicInterior.Point k M),
    w ∈ (chartAt (Model (k + 1)) anchor).source →
    (s.val, chartAt (Model (k + 1)) anchor w) ∈ domain → ∀ v,
    coframe (s.val, chartAt (Model (k + 1)) anchor w)
      (originalInteriorComplexInChart hδ C hemb hboundary hzero J anchor (s, w) v) =
    coordinateComplexStructure n (coframe (s.val, chartAt (Model (k + 1)) anchor w) v)

variable
  (hC : ∀ t, ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) (𝓡∂ (k + 1)) ∞ (C t)
    (Half δ (IntrinsicBoundary.Point k M)))
  (hinv : ∀ t p, p ∈ Half δ (IntrinsicBoundary.Point k M) →
    ∃ g : M → ℝ × IntrinsicBoundary.Point k M,
      ContMDiffAt (𝓡∂ (k + 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model k)) ∞ g (C t p) ∧
        ∀ᶠ q in 𝓝[Half δ (IntrinsicBoundary.Point k M)] p, g (C t q) = q)

include P hC hinv in
theorem exists_originalInteriorCanonicalChart
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (p : Parameter × IntrinsicInterior.Point k M) :
    ∃ c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n),
      c.anchor = p.2 ∧ (p.1.val, chartAt (Model (k + 1)) c.anchor p.2) ∈ c.domain := by
  obtain ⟨U, K, hpU, hK, heK⟩ := hJ p.1 p.2
  let e := chartAt (Model (k + 1)) p.2
  let V : Set (ℝ × Model (k + 1)) := (U : Set _) ∩ (univ ×ˢ e.target)
  have hV : IsOpen V := U.isOpen.inter (isOpen_univ.prod e.open_target)
  have hpV : (p.1.val, e p.2) ∈ V :=
    ⟨hpU, mem_univ _, e.map_source (mem_chart_source _ p.2)⟩
  have hsq : ∀ z ∈ V ∩ (parameterInterval ×ˢ (univ : Set (Model (k + 1)))),
      ∀ v, K z (K z v) = -v := by
    intro z hz v
    let t : Parameter := ⟨z.1, hz.2.1⟩
    let w := e.symm z.2
    have hw : w ∈ e.source := e.map_target hz.1.2.2
    have hew : chartAt (Model (k + 1)) p.2 w = z.2 := e.right_inv hz.1.2.2
    have hmatch := heK t w hw (by
      change (t.val, chartAt (Model (k + 1)) p.2 w) ∈ U.carrier
      rw [hew]
      exact hz.1.1)
    have hmatch' : K z = originalInteriorComplexInChart hδ C hemb hboundary hzero J p.2 (t, w) := by
      simpa only [t, hew, Prod.mk.eta] using hmatch
    rw [hmatch']
    let H := originalInteriorCanonicalDifferential hδ (C t) (hemb t) (hboundary t) (hzero t) p.2 w
    have hHi : H.IsInvertible := isInvertible_originalInteriorCanonicalDifferential
      hδ (C t) (hemb t) (hC t) (hboundary t) (hinv t) (hzero t) p.2 w hw
    change H (J t _ (H.inverse (H (J t _ (H.inverse v))))) = -v
    rw [hHi.inverse_apply_self, hJsq, map_neg, hHi.self_apply_inverse]
  obtain ⟨b, hbV, hpb⟩ := exists_nativeCoordinateCanonicalPatch P hV hpV
    (show (p.1.val, e p.2) ∈ parameterInterval ×ˢ (univ : Set (Model (k + 1))) from
      ⟨p.1.property, mem_univ _⟩) (hK.mono inter_subset_left) hsq
  refine ⟨{
    anchor := p.2
    domain := b.domain
    subset_target := fun _ hz => (hbV hz).2
    coframe := b.coframe
    smooth_coframe := b.smooth_coframe
    invertible_coframe := b.invertible_coframe
    intertwines := ?_ }, rfl, hpb⟩
  intro s w hw hwb v
  rw [← heK s w hw (hbV hwb).1]
  exact b.intertwines _ ⟨hwb, s.property, mem_univ _⟩ v

/-- The original complex field alone selects an interior canonical cover. -/
def originalInteriorCanonicalChartAt
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (p : Parameter × IntrinsicInterior.Point k M) :=
  (exists_originalInteriorCanonicalChart hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).choose


namespace OriginalInteriorCanonicalChart

variable (c : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
variable {hδ C hemb hboundary hzero J}

/-- This is the existing total family's interior patch base. -/
def baseDomain : Set (Parameter × IntrinsicInterior.Point k M) :=
  (univ ×ˢ (chartAt (Model (k + 1)) c.anchor).source) ∩
    (fun p => (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)) ⁻¹' c.domain

/-- All canonical slots are spatial. The original inclusion derivative is
part of the coframe, and is never an independently supplied map. -/
def nativeCoframe (P : Model (2 * n) ≃L[ℝ] Model (k + 1))
    (p : Parameter × IntrinsicInterior.Point k M) :
    Model (2 * n) →L[ℝ] TangentCoordinates n :=
  ((c.coframe (p.1.val, chartAt (Model (k + 1)) c.anchor p.2)).comp
    (originalInteriorCanonicalDifferential hδ (C p.1) (hemb p.1)
      (hboundary p.1) (hzero p.1) c.anchor p.2)).comp P.toContinuousLinearMap

theorem isOpen_baseDomain : IsOpen c.baseDomain := by
  let e := chartAt (Model (k + 1)) c.anchor
  have hc : ContinuousOn (fun p : Parameter × IntrinsicInterior.Point k M =>
      (p.1.val, e p.2)) (univ ×ˢ e.source) :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      (e.continuousOn.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  exact hc.isOpen_inter_preimage (isOpen_univ.prod e.open_source) c.domain.isOpen

include hC hinv in
theorem invertible_nativeCoframe {p : Parameter × IntrinsicInterior.Point k M}
    (hp : p ∈ c.baseDomain) : (c.nativeCoframe P p).IsInvertible :=
  ((c.invertible_coframe _ hp.2).comp
    (isInvertible_originalInteriorCanonicalDifferential hδ (C p.1) (hemb p.1) (hC p.1)
      (hboundary p.1) (hinv p.1) (hzero p.1) c.anchor p.2 hp.1.2)).comp ⟨P, rfl⟩

include hC hinv in
theorem nativeCoframe_intertwines {p : Parameter × IntrinsicInterior.Point k M}
    (hp : p ∈ c.baseDomain) (v : Model (2 * n)) :
    c.nativeCoframe P p (originalInteriorComplex C J P p v) =
      coordinateComplexStructure n (c.nativeCoframe P p v) := by
  let H := originalInteriorCanonicalDifferential hδ (C p.1) (hemb p.1)
    (hboundary p.1) (hzero p.1) c.anchor p.2
  have hHi : H.IsInvertible := isInvertible_originalInteriorCanonicalDifferential
    hδ (C p.1) (hemb p.1) (hC p.1) (hboundary p.1) (hinv p.1) (hzero p.1)
    c.anchor p.2 hp.1.2
  have h := c.intertwines p.1 p.2 hp.1.2 hp.2 (H (P v))
  dsimp only [originalInteriorComplexInChart, ContinuousLinearMap.comp_apply] at h
  rw [hHi.inverse_apply_self] at h
  simpa only [nativeCoframe, originalInteriorComplex, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h


variable {P}

def lineCoordinateLinearMap (x : Parameter × IntrinsicInterior.Point k M) : canonicalSubmodule (originalInteriorComplex C J P x) →ₗ[ℂ] ℂ where
  toFun s := canonicalCoframeCoefficient (c.nativeCoframe P x) s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lineCoordinateEquiv (x : Parameter × IntrinsicInterior.Point k M) (hx : x ∈ c.baseDomain) :
    canonicalSubmodule (originalInteriorComplex C J P x) ≃ₗ[ℂ] ℂ where
  toLinearMap := c.lineCoordinateLinearMap (P := P) x
  invFun q := q • (⟨coframeCanonicalGenerator (c.nativeCoframe P x),
    coframeCanonicalGenerator_canonical _ (c.invertible_nativeCoframe (P := P) hC hinv hx) _
      (c.nativeCoframe_intertwines (P := P) hC hinv hx)⟩ : canonicalSubmodule (originalInteriorComplex C J P x))
  left_inv s := Subtype.ext (canonicalCoframe_reconstruction _
    (c.invertible_nativeCoframe (P := P) hC hinv hx) _ (c.nativeCoframe_intertwines (P := P) hC hinv hx) _ s.property).symm
  right_inv q := by
    change q * canonicalCoframeCoefficient (c.nativeCoframe P x)
      (coframeCanonicalGenerator (c.nativeCoframe P x)) = q
    rw [coframeCanonicalGenerator_frame _ (c.invertible_nativeCoframe (P := P) hC hinv hx), mul_one]

/-- The coordinate is the tensor product of two unsquared line
coordinates, independently of natural square multiplication. -/
def tensorCoordinateLinearMap (x : Parameter × IntrinsicInterior.Point k M) : CanonicalTensorSquare (originalInteriorComplex C J P x) →ₗ[ℂ] ℂ :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp
    (TensorProduct.map (c.lineCoordinateLinearMap (P := P) x) (c.lineCoordinateLinearMap (P := P) x))

def tensorCoordinateEquiv (x : Parameter × IntrinsicInterior.Point k M) (hx : x ∈ c.baseDomain) :
    CanonicalTensorSquare (originalInteriorComplex C J P x) ≃ₗ[ℂ] ℂ :=
  (TensorProduct.congr (c.lineCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx) (c.lineCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx)).trans
    (TensorProduct.lid ℂ ℂ)

@[simp] theorem tensorCoordinateEquiv_toLinearMap (x : Parameter × IntrinsicInterior.Point k M) (hx : x ∈ c.baseDomain) :
    (c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx).toLinearMap = c.tensorCoordinateLinearMap (P := P) x := rfl

def tensorCoordinateContinuousEquiv (x : Parameter × IntrinsicInterior.Point k M) (hx : x ∈ c.baseDomain) :
    CanonicalTensorSquare (originalInteriorComplex C J P x) ≃L[ℂ] ℂ where
  toLinearEquiv := c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx
  continuous_toFun := IsModuleTopology.continuous_of_linearMap _
  continuous_invFun := by
    change Continuous (c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx).symm.toLinearMap
    exact IsModuleTopology.continuous_of_linearMap _

/-- The bridge is an equality of the independently constructed scalar
coordinates, proved on pure tensors and extended by tensor linearity. -/
theorem coefficient_squareMap (x : Parameter × IntrinsicInterior.Point k M) (t : CanonicalTensorSquare (originalInteriorComplex C J P x)) :
    squaredCoframeCoefficient (c.nativeCoframe P x) (canonicalSquareMap (originalInteriorComplex C J P x) t).val =
      c.tensorCoordinateLinearMap (P := P) x t := by
  let L : squaredCanonicalSubmodule (originalInteriorComplex C J P x) →ₗ[ℂ] ℂ :=
    { toFun s := squaredCoframeCoefficient (c.nativeCoframe P x) s.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h : L.comp (canonicalSquareMap (originalInteriorComplex C J P x)) = c.tensorCoordinateLinearMap (P := P) x := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro s
    apply LinearMap.ext
    intro u
    change squaredCoframeCoefficient (c.nativeCoframe P x)
      (canonicalSquareMap (originalInteriorComplex C J P x) (s ⊗ₜ[ℂ] u)).val =
      canonicalCoframeCoefficient (c.nativeCoframe P x) s.val *
        canonicalCoframeCoefficient (c.nativeCoframe P x) u.val
    rw [canonicalSquareMap_tmul]
    simp only [squaredCoframeCoefficient, canonicalTensorProduct_apply,
      canonicalCoframeCoefficient, Sum.elim_inl, Sum.elim_inr, id_eq]
  exact congrArg (fun f => f t) h

open scoped Classical in
def tensorPretrivialization : Pretrivialization ℂ
    (π ℂ (fun x : (Parameter × IntrinsicInterior.Point k M) => CanonicalTensorSquare (originalInteriorComplex C J P x))) where
  toFun p := (p.proj, c.tensorCoordinateLinearMap (P := P) p.proj p.snd)
  invFun p := if hp : p.1 ∈ c.baseDomain then
    ⟨p.1, (c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) p.1 hp).symm p.2⟩ else ⟨p.1, 0⟩
  source := (π ℂ (fun x : (Parameter × IntrinsicInterior.Point k M) => CanonicalTensorSquare (originalInteriorComplex C J P x))) ⁻¹' c.baseDomain
  target := c.baseDomain ×ˢ univ
  map_source' p hp := ⟨hp, mem_univ _⟩
  map_target' p hp := by simp only [dite_eq_left hp.1]; exact hp.1
  left_inv' p hp := by
    rcases p with ⟨x, s⟩
    change x ∈ c.baseDomain at hp
    dsimp only
    rw [dite_eq_left hp]
    exact congrArg (fun t : CanonicalTensorSquare (originalInteriorComplex C J P x) =>
      (⟨x, t⟩ : Bundle.TotalSpace ℂ (fun x => CanonicalTensorSquare (originalInteriorComplex C J P x))))
      ((c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hp).symm_apply_apply s)
  right_inv' p hp := by
    rw [dite_eq_left hp.1]
    exact Prod.ext rfl ((c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) p.1 hp.1).apply_symm_apply p.2)
  open_target := c.isOpen_baseDomain.prod isOpen_univ
  baseSet := c.baseDomain
  open_baseSet := c.isOpen_baseDomain
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

instance tensorPretrivialization_complexLinear : c.tensorPretrivialization (P := P) (hC := hC) (hinv := hinv).IsLinear ℂ where
  linear x _ := (c.tensorCoordinateLinearMap (P := P) x).isLinear

instance tensorPretrivialization_realLinear : c.tensorPretrivialization (P := P) (hC := hC) (hinv := hinv).IsLinear ℝ where
  linear x _ := ((c.tensorCoordinateLinearMap (P := P) x).restrictScalars ℝ).isLinear

theorem tensorPretrivialization_symm {x : (Parameter × IntrinsicInterior.Point k M)} (hx : x ∈ c.baseDomain) (q : ℂ) :
    c.tensorPretrivialization (P := P) (hC := hC) (hinv := hinv).symm x q = (c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx).symm q := by
  apply (c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx).injective
  rw [(c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx).apply_symm_apply]
  exact congrArg Prod.snd (c.tensorPretrivialization (P := P) (hC := hC) (hinv := hinv).apply_mk_symm hx q)

theorem tensorPretrivialization_isInducing {x : (Parameter × IntrinsicInterior.Point k M)} (hx : x ∈ c.baseDomain) :
    Topology.IsInducing (c.tensorPretrivialization (P := P) (hC := hC) (hinv := hinv) ∘ Bundle.TotalSpace.mk x) := by
  have h := (c.tensorCoordinateContinuousEquiv (P := P) (hC := hC) (hinv := hinv) x hx).toHomeomorph.isInducing
  change Topology.IsInducing (c.tensorCoordinateEquiv (P := P) (hC := hC) (hinv := hinv) x hx).toLinearMap at h
  rw [c.tensorCoordinateEquiv_toLinearMap] at h
  have hlin : Continuous (c.tensorCoordinateLinearMap (P := P) x) :=
    IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous (c.tensorPretrivialization (P := P) (hC := hC) (hinv := hinv) ∘ Bundle.TotalSpace.mk x) :=
    continuous_const.prodMk hlin
  exact Topology.IsInducing.of_comp hc continuous_snd h

include hC hinv in
theorem reconstruction {x : Parameter × IntrinsicInterior.Point k M} (hx : x ∈ c.baseDomain)
    (s : squaredCanonicalSubmodule (originalInteriorComplex C J P x)) :
    s.val = squaredCoframeCoefficient (c.nativeCoframe P x) s.val •
      coframeSquaredGenerator (c.nativeCoframe P x) :=
  squaredCoframe_reconstruction _ (c.invertible_nativeCoframe (P := P) hC hinv hx) _
    (c.nativeCoframe_intertwines (P := P) hC hinv hx) _ s.property

def transition (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : Parameter × IntrinsicInterior.Point k M) : ℂ :=
  squaredCoframeTransition (c.nativeCoframe P x) (d.nativeCoframe P x)

theorem tensorTransition_apply
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : Parameter × IntrinsicInterior.Point k M} (hx : x ∈ c.baseDomain ∩ d.baseDomain) (q : ℂ) :
    (d.tensorPretrivialization (P := P) hC hinv
      ⟨x, (c.tensorPretrivialization (P := P) hC hinv).symm x q⟩).2 =
      c.transition (P := P) d x * q := by
  rw [c.tensorPretrivialization_symm hC hinv hx.1]
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv hC hinv x hx.1).symm q) = _
  rw [← d.coefficient_squareMap]
  have hr := c.reconstruction hC hinv hx.1
    (canonicalSquareMap (originalInteriorComplex C J P x) ((c.tensorCoordinateEquiv hC hinv x hx.1).symm q))
  have hq : squaredCoframeCoefficient (c.nativeCoframe P x)
      (canonicalSquareMap (originalInteriorComplex C J P x) ((c.tensorCoordinateEquiv hC hinv x hx.1).symm q)).val = q := by
    rw [c.coefficient_squareMap]
    exact (c.tensorCoordinateEquiv hC hinv x hx.1).apply_symm_apply q
  rw [hq] at hr
  rw [hr]
  change q * squaredCoframeCoefficient (d.nativeCoframe P x)
    (coframeSquaredGenerator (c.nativeCoframe P x)) = _
  exact mul_comm _ _


/-- The overlap in the denominator chart's genuine real coordinates. -/
def transitionDomain
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    Set (ℝ × Model (k + 1)) :=
  (univ ×ˢ originalInteriorCoordinateOverlap d.anchor c.anchor) ∩
    (fun p => (p.1, chartAt (Model (k + 1)) c.anchor
      ((chartAt (Model (k + 1)) d.anchor).symm p.2))) ⁻¹' c.domain ∩ d.domain

def transitionExtension
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (p : ℝ × Model (k + 1)) : ℂ :=
  squaredCoframeTransition
    (((c.coframe (p.1, chartAt (Model (k + 1)) c.anchor
      ((chartAt (Model (k + 1)) d.anchor).symm p.2))).comp
      (fderiv ℝ ((chartAt (Model (k + 1)) c.anchor) ∘
        (chartAt (Model (k + 1)) d.anchor).symm) p.2)).comp P.toContinuousLinearMap)
    ((d.coframe p).comp P.toContinuousLinearMap)

theorem smooth_transitionExtension
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContDiffOn ℝ ∞ (c.transitionExtension (P := P) d) (c.transitionDomain d) :=
  contDiffOn_originalInteriorSquaredTransition P d.anchor c.anchor
    (d.smooth_coframe.mono inter_subset_right) c.smooth_coframe
    (fun _ hp => hp.1.1) (fun _ hp => hp.1.2)
    (fun _ hp => d.invertible_coframe _ hp.2)

include hC hinv in
theorem smooth_transition
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ) ∞
      (c.transition (P := P) d) (c.baseDomain ∩ d.baseDomain) := by
  let e := chartAt (Model (k + 1)) d.anchor
  let z := fun p : Parameter × IntrinsicInterior.Point k M => (p.1.val, e p.2)
  have ht : ContMDiff (familyModel (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Parameter × IntrinsicInterior.Point k M => p.1.val) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_fst
  have hx : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞
      (fun p : Parameter × IntrinsicInterior.Point k M => e p.2)
      (c.baseDomain ∩ d.baseDomain) :=
    (contMDiffOn_chart (I := 𝓘(ℝ, Model (k + 1))) (x := d.anchor)).comp
      contMDiff_snd.contMDiffOn (fun _ hp => hp.2.1.2)
  have hz : ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℝ × Model (k + 1)) ∞ z
      (c.baseDomain ∩ d.baseDomain) := ht.contMDiffOn.prodMk_space hx
  have hzD : MapsTo z (c.baseDomain ∩ d.baseDomain) (c.transitionDomain d) := by
    intro p hp
    refine ⟨⟨⟨mem_univ _, e.map_source hp.2.1.2, ?_⟩, ?_⟩, hp.2.2⟩
    · change e.symm (e p.2) ∈ (chartAt (Model (k + 1)) c.anchor).source
      rw [e.left_inv hp.2.1.2]
      exact hp.1.1.2
    · change (p.1.val, chartAt (Model (k + 1)) c.anchor (e.symm (e p.2))) ∈ c.domain
      rw [e.left_inv hp.2.1.2]
      exact hp.1.2
  apply ((c.smooth_transitionExtension (P := P) d).contMDiffOn.comp hz hzD).congr
  intro p hp
  change c.transition (P := P) d p = c.transitionExtension (P := P) d (z p)
  dsimp only [transition, nativeCoframe, transitionExtension, z]
  rw [e.left_inv hp.2.1.2]
  exact originalInteriorCanonical_squaredTransition hδ (C p.1) (hemb p.1) (hC p.1)
    (hboundary p.1) (hinv p.1) (hzero p.1) P d.anchor c.anchor p.2
    hp.2.1.2 hp.1.1.2 _ _


def transitionMap
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    (x : Parameter × IntrinsicInterior.Point k M) : ℂ →L[ℝ] ℂ :=
  c.transition (P := P) d x • ContinuousLinearMap.id ℝ ℂ

include hC hinv in
theorem smooth_transitionMap
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    ContMDiffOn (familyModel (k + 1)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) ∞
      (c.transitionMap (P := P) d) (c.baseDomain ∩ d.baseDomain) := by
  let L : ℂ →L[ℝ] (ℂ →L[ℝ] ℂ) :=
    (ContinuousLinearMap.toSpanSingleton ℂ (ContinuousLinearMap.id ℝ ℂ)).restrictScalars ℝ
  exact L.contMDiff.comp_contMDiffOn (c.smooth_transition (P := P) hC hinv d)

theorem transitionMap_apply
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : Parameter × IntrinsicInterior.Point k M} (hx : x ∈ c.baseDomain ∩ d.baseDomain) (q : ℂ) :
    c.transitionMap (P := P) d x q =
      (d.tensorPretrivialization (P := P) hC hinv
        ⟨x, (c.tensorPretrivialization (P := P) hC hinv).symm x q⟩).2 :=
  (c.tensorTransition_apply hC hinv d hx q).symm

theorem isOpen_transitionDomain
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n)) :
    IsOpen (c.transitionDomain d) := by
  have hg := (contDiffOn_originalInteriorCoordinateTransition d.anchor c.anchor).continuousOn
  have hm : ContinuousOn (fun p : ℝ × Model (k + 1) =>
      (p.1, chartAt (Model (k + 1)) c.anchor ((chartAt (Model (k + 1)) d.anchor).symm p.2)))
      (univ ×ˢ originalInteriorCoordinateOverlap d.anchor c.anchor) :=
    continuous_fst.continuousOn.prodMk
      (hg.comp continuous_snd.continuousOn (fun _ hp => hp.2))
  exact (hm.isOpen_inter_preimage
    (isOpen_univ.prod (isOpen_originalInteriorCoordinateOverlap d.anchor c.anchor))
    c.domain.isOpen).inter d.domain.isOpen

include hC hinv in
/-- All original coframe charts give coordinates on the same native fiber. -/
theorem tensorCoordinateLinearMap_transition
    (d : OriginalInteriorCanonicalChart hδ C hemb hboundary hzero J (n := n))
    {x : Parameter × IntrinsicInterior.Point k M} (hx : x ∈ c.baseDomain ∩ d.baseDomain)
    (τ : CanonicalTensorSquare (originalInteriorComplex C J P x)) :
    d.tensorCoordinateLinearMap x τ = c.transition (P := P) d x * c.tensorCoordinateLinearMap x τ := by
  have h := c.tensorTransition_apply (P := P) hC hinv d hx (c.tensorCoordinateLinearMap x τ)
  rw [c.tensorPretrivialization_symm hC hinv hx.1] at h
  change d.tensorCoordinateLinearMap x ((c.tensorCoordinateEquiv hC hinv x hx.1).symm
    ((c.tensorCoordinateEquiv hC hinv x hx.1) τ)) = _ at h
  rwa [(c.tensorCoordinateEquiv hC hinv x hx.1).symm_apply_apply] at h


end OriginalInteriorCanonicalChart
/-- The cover includes every point of the original interval-interior patch. -/
theorem mem_originalInteriorCanonicalChartAt
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (p : Parameter × IntrinsicInterior.Point k M) :
    p ∈ (originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).baseDomain := by
  have h := (exists_originalInteriorCanonicalChart hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).choose_spec
  refine ⟨⟨mem_univ _, ?_⟩, h.2⟩
  rw [show (originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).anchor = p.2 from h.1]
  exact mem_chart_source _ _

/-- The actual interval-interior tensor-square prebundle. Its atlas consists
of all the original canonical coframe charts, independently of a section or
any encoded Maslov family. -/
def originalInteriorCanonicalTensorSquareVectorPrebundle
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    VectorPrebundle ℝ ℂ (fun x : Parameter × IntrinsicInterior.Point k M =>
      CanonicalTensorSquare (originalInteriorComplex C J P x)) where
  pretrivializationAtlas := Set.range
    (OriginalInteriorCanonicalChart.tensorPretrivialization (P := P) hC hinv)
  pretrivialization_linear' := by
    rintro _ ⟨c, rfl⟩
    infer_instance
  pretrivializationAt p :=
    (originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).tensorPretrivialization hC hinv
  mem_base_pretrivializationAt :=
    mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq
  pretrivialization_mem_atlas p := ⟨_, rfl⟩
  exists_coordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap (P := P) d, (c.smooth_transitionMap hC hinv d).continuousOn,
      fun _ hx q => c.transitionMap_apply hC hinv d hx q⟩
  totalSpaceMk_isInducing p :=
    (originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p).tensorPretrivialization_isInducing hC hinv
      (mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq p)

instance originalInteriorCanonicalTensorSquareVectorPrebundle_isContMDiff
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    (originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq).IsContMDiff
      (familyModel (k + 1)) ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨c.transitionMap (P := P) d, c.smooth_transitionMap hC hinv d,
      fun _ hx q => c.transitionMap_apply hC hinv d hx q⟩

/-- The constructed original interval-interior bundle is smoothly locally
trivial, including both parameter endpoints. -/
theorem originalInteriorCanonicalTensorSquareVectorBundle_smooth
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    let a := originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    letI := a.toVectorBundle
    ContMDiffVectorBundle ∞ ℂ
      (fun x : Parameter × IntrinsicInterior.Point k M => CanonicalTensorSquare (originalInteriorComplex C J P x))
      (familyModel (k + 1)) :=
  (originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq).contMDiffVectorBundle _

/-- The same atlas has complex-linear transitions and defines a complex
line bundle on the original interior base. -/
theorem originalInteriorCanonicalTensorSquareVectorBundle_complex
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v) :
    let a := originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq
    letI := a.totalSpaceTopology
    letI := a.toFiberBundle
    VectorBundle ℂ ℂ
      (fun x : Parameter × IntrinsicInterior.Point k M => CanonicalTensorSquare (originalInteriorComplex C J P x)) := by
  dsimp only
  let a := originalInteriorCanonicalTensorSquareVectorPrebundle hδ C hemb hboundary hzero J P hC hinv hJ hJsq
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
    have hc : ContinuousOn (fun x => L (c.transition (P := P) d x)) (c.baseDomain ∩ d.baseDomain) :=
      L.continuous.comp_continuousOn (c.smooth_transition hC hinv d).continuousOn
    apply hc.congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro q
    simp only [ContinuousLinearEquiv.coe_coe]
    rw [Trivialization.coordChangeL_apply]
    · exact (c.transitionMap_apply hC hinv d hx q).symm
    · exact hx


include hC hinv in
/-- Every original canonical-square fiber is a complex line. -/
theorem originalInteriorCanonicalTensorSquare_finrank
    (hJ : HasOriginalInteriorComplexExtensions hδ C hemb hboundary hzero J)
    (hJsq : ∀ s x v, J s x (J s x v) = -v)
    (x : Parameter × IntrinsicInterior.Point k M) :
    Module.finrank ℂ (CanonicalTensorSquare (originalInteriorComplex C J P x)) = 1 := by
  let c := originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  have hx : x ∈ c.baseDomain :=
    mem_originalInteriorCanonicalChartAt hδ C hemb hboundary hzero J P hC hinv hJ hJsq x
  rw [(c.tensorCoordinateEquiv (P := P) hC hinv x hx).finrank_eq]
  exact Module.finrank_self ℂ


end FsFltz.Geometry.IntrinsicCompletionGluing
