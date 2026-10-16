import FsFltz.Geometry.TailoringRoundedTransport
import FsFltz.Geometry.MarkedFlowEmbedding
import FsFltz.Geometry.TailoringRibbonNonempty
import FsFltz.Geometry.SmoothEmbeddingFactorization
import FsFltz.Geometry.PairFamilyConstruction

/-!
# The same fixed carriers for the actual rounded tailoring pair

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and `eq:normalizedrounding`, lines 1254–1282; `geoemtric-part-fsf.tex`,
`def:chain`, lines 163–169. One constructed pair flow gives the ambient
embedding family. Its composition with one fixed ribbon inclusion gives
the ribbon family on the whole common extension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.SmoothManifold.SmoothEmbedding

/-- The native identity smooth embedding. -/
def identity {d : ℕ} (M : SmoothManifold d) : M.SmoothEmbedding M where
  map := ⟨id, contMDiff_id⟩
  embedding := Topology.IsEmbedding.id
  immersion := by
    intro x
    change Function.Injective (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) id x)
    rw [mfderiv_id]
    exact Function.injective_id

end FsFltz.Geometry.SmoothManifold.SmoothEmbedding

namespace FsFltz
open Geometry
variable {n : ℕ}

local instance roundedPairLGCharts : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance roundedPairLGSmooth : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
local instance roundedPairProdCharts : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
  inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
local instance roundedPairProdSmooth : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
  rw [modelWithCornersSelf_prod]
  exact inferInstanceAs
    (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))

/-- The actual rounded domains and full ribbons have one nested pair of
nonempty native carriers. Both embedding families come from the same flow,
and the ribbon embedding is literally the composition on the whole extension.
The radius threshold is chosen before the outer radius, so the range of
allowed truncations is nonempty. -/
theorem tailoringFamily_exists_uniform_rounded_fixedPair_carriers
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c) (hU : 0 < U)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ F : ℝ, 0 < F ∧ ∀ Cplus : ℝ, F < Cplus →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀, ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (E : CompactDomain (2 * n)) (D : CompactDomain (2 * n - 2))
        (χ : E.extension.SmoothEmbedding (lgManifold n))
        (i : D.extension.SmoothEmbedding E.extension)
        (k : D.extension.SmoothEmbedding E.boundary)
        (Φ : Flow ℝ (ℝ × LGSpace n))
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n)),
        E.carrier.Nonempty ∧ D.carrier.Nonempty ∧
        range i.map ⊆ frontier E.carrier ∧
        (∀ x, E.boundaryInclusion.map (k.map x) = i.map x) ∧
        χ.map '' E.carrier = tailoringRoundedDomain I φ β 0 R (Cplus ^ 2 * β ^ 2 / 2) m ∧
        χ.map '' frontier E.carrier =
          {y | tailoringRoundedDefiningFunction I φ β 0 R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
        (∀ x, (J parameterZero).map x = χ.map x) ∧
        (∀ t x, (J t).map x = (Φ t.val (0, χ.map x)).2) ∧
        E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n)
          (fun t => ((J t).comp i).map) ∧
        ∀ t : Parameter,
          (J t).map '' E.carrier = tailoringRoundedDomain I φ β t.val R
            (Cplus ^ 2 * β ^ 2 / 2) m ∧
          (J t).map '' frontier E.carrier =
            {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
          ((J t).comp i).map '' D.carrier =
            {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
          ((J t).comp i).map '' frontier D.carrier =
            {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} := by
  classical
  obtain ⟨Ft, hFt, htransport⟩ := tailoringFamily_exists_uniform_rounded_pair_transport
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fm, hFm, Bm, hBm, hmark⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fn, hFn, Bn, hBn, hnonempty⟩ := tailoringFamily_exists_uniform_nonempty_fiber_truncations
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max Ft (max Fm Fn)
  have hF : 0 < F := hFt.trans_le (le_max_left _ _)
  refine ⟨F, hF, ?_⟩
  intro Cplus hFCplus
  have hCplus : 0 < Cplus := hF.trans hFCplus
  obtain ⟨Bt, hBt, htransport⟩ := htransport Cplus ((le_max_left _ _).trans_lt hFCplus)
  obtain ⟨Bo, hBo, hout⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend hCplus
  let β₀ := max Bt (max Bo (max Bm Bn))
  refine ⟨β₀, hBt.trans_le (le_max_left _ _), ?_⟩
  intro β hβ R hR Aminus hAminus hA
  have hβt : Bt ≤ β := (le_max_left _ _).trans hβ
  have hβo : Bo ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβm : Bm ≤ β := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hβn : Bn ≤ β := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hβ))
  have hAt : Ft ^ 2 * β ^ 2 / 2 ≤ Aminus := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFt.le (le_max_left _ _) 2) (sq_nonneg β)) hAminus
  have hAm : Fm ^ 2 * β ^ 2 / 2 ≤ Aminus := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFm.le ((le_max_left _ _).trans (le_max_right _ _)) 2)
      (sq_nonneg β)) hAminus
  have hAn : Fn ^ 2 * β ^ 2 / 2 ≤ Aminus := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFn.le ((le_max_right _ _).trans (le_max_right _ _)) 2)
      (sq_nonneg β)) hAminus
  obtain ⟨δt, hδt, hδtgap, htransport⟩ := htransport β hβt R hR Aminus hAt hA
  obtain ⟨K, _hK, hout⟩ := hout β hβo
  obtain ⟨δo, hδo, _hδogap, hout⟩ := hout R hR Aminus hA
  let δ := min δt δo
  refine ⟨δ, lt_min hδt hδo, (min_le_left _ _).trans_lt hδtgap, ?_⟩
  intro m hm hmd
  have hmdt : m.eps ≤ δt := hmd.trans (min_le_left _ _)
  have hmdo : m.eps ≤ δo := hmd.trans (min_le_right _ _)
  let A := Cplus ^ 2 * β ^ 2 / 2
  have hgap : Aminus < A - m.eps := by
    change δt < A - Aminus at hδtgap
    linarith
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  let ρ : LGSpace n → ℝ := tailoringRoundedDefiningFunction I φ β 0 R A m
  let α := (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β 0) K
  have hρ := contMDiff_tailoringRoundedDefiningFunction I hφ β 0 R A m
  have hcompact := isCompact_tailoringRoundedDomain I hφ β 0 A hR m
    (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend A)
  have hreg : ∀ y : (lgManifold n).Point, ρ y = 0 →
      mfderiv 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ρ y ≠ 0 :=
    regular_zero_of_scalarDerivative_pos (lgManifold n) ρ
      ((lgManifold n).liouvilleVector α) (by
        intro y hy
        exact hout m hm hmdo K le_rfl 0 hzero y
          (tailoringRoundedDomain_subset I φ β 0 A hR m hy.le).1 hy.ge)
  let Ebase := regularSublevelCompactDomain (lgManifold n) ρ hρ hcompact hreg
  have hEfront : frontier Ebase.carrier = {y : LGSpace n | ρ y = 0} :=
    regularSublevelCompactDomain_frontier (lgManifold n) ρ hρ hcompact hreg
  obtain ⟨N, j, P, himage, hlevels⟩ := hmark β hβm 0 hzero
  obtain ⟨hpos, hDimage, _hcompletion, _hmarking⟩ := hlevels Aminus hAm
  let Dbase := (tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend
    I β 0 j himage P Aminus hpos).domain
  have hDcarrier : Dbase.carrier = {x | φ (j.map x).1 ≤ Aminus} :=
    tailoringFiberOutwardDomain_carrier hφ hEnd1 hEnd hhom hc hlower hL hend
      I β 0 j himage P Aminus hpos
  have hDfront : frontier Dbase.carrier = {x | φ (j.map x).1 = Aminus} :=
    tailoringFiberOutwardDomain_frontier hφ hEnd1 hEnd hhom hc hlower hL hend
      I β 0 j himage P Aminus hpos
  have hDne : Dbase.carrier.Nonempty := by
    obtain ⟨y, hy⟩ := hnonempty β hβn 0 hzero Aminus hAn
    have hyD : y ∈ j.map '' Dbase.carrier := by rwa [hDimage]
    obtain ⟨x, hx, _⟩ := hyD
    exact ⟨x, hx⟩
  have hbase (x : N.Point) : tailoringFamily I β 0 (j.map x) = 1 := by
    have hx : j.map x ∈ range j.map := ⟨x, rfl⟩
    rwa [himage] at hx
  obtain ⟨Φ, hΦ, hambient, hribbon⟩ := htransport m hm hmdt
  have htime : ∀ t ∈ parameterInterval, ∀ x ∈ Ebase.carrier,
      (Φ t (0, x)).1 = t := by
    intro t ht x hx
    simpa only [zero_add] using
      (hambient (0, x) hzero hx t (by simpa only [zero_add, parameterInterval] using ht)).1
  rw [modelWithCornersSelf_prod] at hΦ
  obtain ⟨Ua, hEUa, J, hJformula, hJ⟩ := exists_uniform_projectedFlow_embedding_neighborhood
    Ebase (lgManifold n) (SmoothManifold.SmoothEmbedding.identity (lgManifold n)) Φ hΦ htime
  change TopologicalSpace.Opens (lgManifold n).Point at Ua
  let E := Ebase.restrict Ua hEUa
  let χ := (lgManifold n).restrictInclusion Ua
  let Ur : TopologicalSpace.Opens Dbase.extension.Point :=
    ⟨{x | j.map x ∈ Ua ∧ φ (j.map x).1 < A - m.eps},
      (Ua.isOpen.preimage j.map.contMDiff.continuous).inter
        (isOpen_lt ((contMDiff_potentialValue hφ).comp j.map.contMDiff).continuous continuous_const)⟩
  have hDUr : Dbase.carrier ⊆ Ur := by
    intro x hx
    have hxφ : φ (j.map x).1 ≤ Aminus := by rwa [hDcarrier] at hx
    refine ⟨?_, hxφ.trans_lt hgap⟩
    apply hEUa
    exact (tailoringRoundedDefiningFunction_eq_zero_on_truncated_fiber
      I hφ β R A Aminus m hm hgap 0 (j.map x) (hbase x) hxφ).le
  let D := Dbase.restrict Ur hDUr
  let jr := j.comp (Dbase.extension.restrictInclusion Ur)
  obtain ⟨i, hi⟩ := exists_smoothEmbedding_factor E.extension D.extension (lgManifold n) χ jr (by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨j.map x.val, x.property.1⟩, rfl⟩)
  have hirange : range i.map ⊆ frontier E.carrier := by
    rintro y ⟨x, rfl⟩
    rw [Ebase.frontier_restrict_carrier Ua]
    change (i.map x).val ∈ frontier Ebase.carrier
    rw [hEfront]
    change ρ (χ.map (i.map x)) = 0
    erw [hi]
    exact tailoringRoundedDefiningFunction_eq_zero_on_truncated_fiber
      I hφ β R A (φ (j.map x.val).1) m hm x.property.2 0 (j.map x.val) (hbase x.val) le_rfl
  obtain ⟨k, hk⟩ := exists_smoothEmbedding_factor E.boundary D.extension E.extension
    E.boundaryInclusion i (by rw [E.boundary_range]; exact hirange)
  have hDne' : D.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDne
    exact ⟨⟨x, hDUr hx⟩, hx⟩
  have hEne : E.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hDne'
    exact ⟨i.map x, E.compact.isClosed.frontier_subset (hirange ⟨x, rfl⟩)⟩
  have hχcarrier : χ.map '' E.carrier = tailoringRoundedDomain I φ β 0 R A m :=
    Ebase.image_restrict_carrier Ua hEUa
  have hχfront : χ.map '' frontier E.carrier = {y : LGSpace n | ρ y = 0} := by
    rw [Ebase.frontier_restrict_carrier Ua]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact (Set.ext_iff.mp hEfront x.val).mp hx
    · intro hy
      have hyfront : y ∈ frontier Ebase.carrier := by rwa [hEfront]
      exact ⟨⟨y, hEUa (Ebase.compact.isClosed.frontier_subset hyfront)⟩, hyfront, rfl⟩
  have hR : D.extension.IsSmoothIntervalMapFamily (lgManifold n)
      (fun t => ((J t).comp i).map) :=
    D.extension.isSmoothIntervalMapFamily_comp_of_contMDiff_family E.extension (lgManifold n)
      (fun t => (J t).map) hJ (fun _ x => i.map x)
      (i.map.contMDiff.comp contMDiff_snd)
  refine ⟨E, D, χ, i, k, Φ, J, hEne, hDne', hirange, hk, hχcarrier, hχfront, ?_,
    hJformula, hJ, hR, ?_⟩
  · intro x
    rw [hJformula]
    simp only [parameterZero, Flow.map_zero_apply]
    rfl
  · intro t
    have hforwardE (x : Ua) (hx : x.val ∈ Ebase.carrier) :
        (J t).map x ∈ tailoringRoundedDomain I φ β t.val R A m ∧
          (tailoringRoundedDefiningFunction I φ β t.val R A m ((J t).map x) = 0 ↔ ρ x.val = 0) := by
      have h := hambient (0, x.val) hzero hx t.val
        (by simpa only [zero_add] using t.property)
      have htime' : (Φ t.val (0, x.val)).1 = t.val := by simpa only [zero_add] using h.1
      rw [htime'] at h
      rw [hJformula]
      exact ⟨h.2.1, h.2.2⟩
    have hbackE (y : LGSpace n) (hy : y ∈ tailoringRoundedDomain I φ β t.val R A m) :
        ∃ x : Ua, x.val ∈ Ebase.carrier ∧ (J t).map x = y ∧
          (ρ x.val = 0 ↔ tailoringRoundedDefiningFunction I φ β t.val R A m y = 0) := by
      have h := hambient (t.val, y) t.property hy (-t.val)
        (by simpa only [add_neg_cancel] using hzero)
      have ht0 : (Φ (-t.val) (t.val, y)).1 = 0 := by simpa only [add_neg_cancel] using h.1
      rw [ht0] at h
      let z := (Φ (-t.val) (t.val, y)).2
      have hz : z ∈ Ebase.carrier := h.2.1
      let x : Ua := ⟨z, hEUa hz⟩
      have hp : (0, z) = Φ (-t.val) (t.val, y) := Prod.ext ht0.symm rfl
      refine ⟨x, hz, ?_, h.2.2⟩
      rw [hJformula]
      change (Φ t.val (0, z)).2 = y
      rw [hp, ← Φ.map_add, add_neg_cancel, Flow.map_zero_apply]
    have hRformula (x : Ur) : ((J t).comp i).map x = (Φ t.val (0, j.map x.val)).2 := by
      change (J t).map (i.map x) = _
      rw [hJformula]
      change (Φ t.val (0, χ.map (i.map x))).2 = _
      erw [hi]
      rfl
    have hforwardR (x : Ur) (hx : x.val ∈ Dbase.carrier) :
        tailoringFamily I β t.val (((J t).comp i).map x) = 1 ∧
          φ (((J t).comp i).map x).1 ≤ Aminus ∧
          (φ (((J t).comp i).map x).1 = Aminus ↔ φ (j.map x.val).1 = Aminus) := by
      have hxφ : φ (j.map x.val).1 ≤ Aminus := by rwa [hDcarrier] at hx
      have h := hribbon (0, j.map x.val) hzero (hbase x.val) hxφ t.val
        (by simpa only [zero_add] using t.property)
      have htime' : (Φ t.val (0, j.map x.val)).1 = t.val := by simpa only [zero_add] using h.1
      rw [htime'] at h
      rw [hRformula]
      exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
    have hbackR (y : LGSpace n) (hy : tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus) :
        ∃ x : Ur, x.val ∈ Dbase.carrier ∧ ((J t).comp i).map x = y ∧
          (φ (j.map x.val).1 = Aminus ↔ φ y.1 = Aminus) := by
      have h := hribbon (t.val, y) t.property hy.1 hy.2 (-t.val)
        (by simpa only [add_neg_cancel] using hzero)
      have ht0 : (Φ (-t.val) (t.val, y)).1 = 0 := by simpa only [add_neg_cancel] using h.1
      rw [ht0] at h
      have hy0 : (Φ (-t.val) (t.val, y)).2 ∈ j.map '' Dbase.carrier := by
        rw [hDimage]
        exact ⟨h.2.1, h.2.2.1⟩
      obtain ⟨z, hz, heq⟩ := hy0
      let x : Ur := ⟨z, hDUr hz⟩
      have hp : (0, j.map z) = Φ (-t.val) (t.val, y) := Prod.ext ht0.symm heq
      refine ⟨x, hz, ?_, ?_⟩
      · rw [hRformula]
        change (Φ t.val (0, j.map z)).2 = y
        rw [hp, ← Φ.map_add, add_neg_cancel, Flow.map_zero_apply]
      · simpa only [x, heq] using h.2.2.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩; exact (hforwardE x hx).1
      · intro hy; obtain ⟨x, hx, heq, _⟩ := hbackE y hy; exact ⟨x, hx, heq⟩
    · rw [Ebase.frontier_restrict_carrier Ua]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hforwardE x (Ebase.compact.isClosed.frontier_subset hx)).2.mpr
          ((Set.ext_iff.mp hEfront x.val).mp hx)
      · intro hy
        obtain ⟨x, hx, heq, heq0⟩ := hbackE y hy.le
        exact ⟨x, (Set.ext_iff.mp hEfront x.val).mpr (heq0.mpr hy), heq⟩
    · ext y
      constructor
      · rintro ⟨x, hx, rfl⟩; exact ⟨(hforwardR x hx).1, (hforwardR x hx).2.1⟩
      · intro hy; obtain ⟨x, hx, heq, _⟩ := hbackR y hy; exact ⟨x, hx, heq⟩
    · rw [Dbase.frontier_restrict_carrier Ur]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hxφ : φ (j.map x.val).1 = Aminus := by rwa [hDfront] at hx
        have hxD := Dbase.compact.isClosed.frontier_subset hx
        exact ⟨(hforwardR x hxD).1, (hforwardR x hxD).2.2.mpr hxφ⟩
      · intro hy
        obtain ⟨x, hx, heq, heqA⟩ := hbackR y ⟨hy.1, hy.2.le⟩
        refine ⟨x, ?_, heq⟩
        change x.val ∈ frontier Dbase.carrier
        rw [hDfront]
        exact heqA.mpr hy.2

end FsFltz
