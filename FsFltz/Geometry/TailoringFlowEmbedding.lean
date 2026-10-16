import FsFltz.Geometry.TailoringHorizontalFlow
import FsFltz.Geometry.MarkedFlowEmbedding
import FsFltz.Geometry.TailoringRibbonNonempty

/-!
# One fixed compact carrier for the actual tailoring ribbon family

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–1009,
and `eq:fiberends`, lines 1230–1237. The base domain is the constructed full
fiber truncation at zero. Every later embedding is the spatial projection
of the same constructed horizontal flow, on one common open extension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz
open Geometry

variable {n : ℕ}

/-- The literal tailored ribbons have one constructed nonempty compact
carrier and one jointly smooth embedding family on a common open extension.
Both entire images and boundary images are literal equation subsets, and
the embeddings retain the exact formula of the constructed horizontal flow. -/
theorem tailoringFamily_exists_uniform_fixedCarrier_embeddings
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
    ∃ F : ℝ, 0 < F ∧ ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ β ≥ β₀, ∀ A : ℝ, F ^ 2 * β ^ 2 / 2 ≤ A →
      ∃ (D : CompactDomain (2 * n - 2)) (j : D.extension.SmoothEmbedding (lgManifold n))
        (Φ : Flow ℝ (ℝ × LGSpace n))
        (V : TopologicalSpace.Opens D.extension.Point) (_hDV : D.carrier ⊆ V)
        (J : Parameter → (D.extension.restrict V).SmoothEmbedding (lgManifold n)),
        range j.map = {y | tailoringFamily I β 0 y = 1} ∧
        j.map '' D.carrier = {y | tailoringFamily I β 0 y = 1 ∧ φ y.1 ≤ A} ∧
        D.carrier.Nonempty ∧
        (∀ t x, (J t).map x = (Φ t.val (0, j.map x.val)).2) ∧
        (D.extension.restrict V).IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        ∀ t : Parameter,
          (J t).map '' (Subtype.val ⁻¹' D.carrier) =
            {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
          (J t).map '' frontier (Subtype.val ⁻¹' D.carrier) =
            {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A} := by
  obtain ⟨Ft, hFt, Bt, hBt, htransport⟩ := tailoringFamily_exists_uniform_compact_transport
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fm, hFm, Bm, hBm, hmark⟩ := tailoringFamily_exists_uniform_fullFiber_markings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Fn, hFn, Bn, hBn, hnonempty⟩ := tailoringFamily_exists_uniform_nonempty_fiber_truncations
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  let F := max Ft (max Fm Fn)
  let β₀ := max Bt (max Bm Bn)
  refine ⟨F, hFt.trans_le (le_max_left _ _), β₀, hBt.trans_le (le_max_left _ _), ?_⟩
  intro β hβ A hA
  have hβt : Bt ≤ β := (le_max_left _ _).trans hβ
  have hβm : Bm ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβn : Bn ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hAt : Ft ^ 2 * β ^ 2 / 2 ≤ A := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFt.le (le_max_left _ _) 2) (sq_nonneg β)) hA
  have hAm : Fm ^ 2 * β ^ 2 / 2 ≤ A := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFm.le ((le_max_left _ _).trans (le_max_right _ _)) 2)
      (sq_nonneg β)) hA
  have hAn : Fn ^ 2 * β ^ 2 / 2 ≤ A := le_trans (by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hFn.le ((le_max_right _ _).trans (le_max_right _ _)) 2)
      (sq_nonneg β)) hA
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨N, j, P, himage, hlevels⟩ := hmark β hβm 0 hzero
  obtain ⟨hpos, hDimage, _hcompletion, _hmarking⟩ := hlevels A hAm
  let D := (tailoringFiberOutwardDomain hφ hEnd1 hEnd hhom hc hlower hL hend
    I β 0 j himage P A hpos).domain
  have hcarrier : D.carrier = {x | φ (j.map x).1 ≤ A} :=
    tailoringFiberOutwardDomain_carrier hφ hEnd1 hEnd hhom hc hlower hL hend
      I β 0 j himage P A hpos
  have hfrontier : frontier D.carrier = {x | φ (j.map x).1 = A} :=
    tailoringFiberOutwardDomain_frontier hφ hEnd1 hEnd hhom hc hlower hL hend
      I β 0 j himage P A hpos
  have hDne : D.carrier.Nonempty := by
    obtain ⟨y, hy⟩ := hnonempty β hβn 0 hzero A hAn
    have hyD : y ∈ j.map '' D.carrier := by rwa [hDimage]
    obtain ⟨x, hx, _⟩ := hyD
    exact ⟨x, hx⟩
  let : ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
  let : IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth
  let : ChartedSpace (ℝ × Model (2 * n)) (ℝ × LGSpace n) :=
    inferInstanceAs (ChartedSpace (ModelProd ℝ (Model (2 * n))) (ℝ × LGSpace n))
  let : IsManifold 𝓘(ℝ, ℝ × Model (2 * n)) ∞ (ℝ × LGSpace n) := by
    rw [modelWithCornersSelf_prod]
    exact inferInstanceAs
      (IsManifold (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model (2 * n))) ∞ (ℝ × LGSpace n))
  obtain ⟨Φ, hΦ, hpres⟩ := htransport β hβt A hAt
  have hbase (x : N.Point) : tailoringFamily I β 0 (j.map x) = 1 := by
    have hx : j.map x ∈ range j.map := ⟨x, rfl⟩
    rwa [himage] at hx
  have htime : ∀ t ∈ parameterInterval, ∀ x ∈ D.carrier,
      (Φ t (0, j.map x)).1 = t := by
    intro t ht x hx
    have hxφ : φ (j.map x).1 ≤ A := by rwa [hcarrier] at hx
    simpa only [zero_add] using (hpres (0, j.map x) hzero (hbase x) hxφ t
      (by simpa only [zero_add, parameterInterval] using ht)).1
  rw [modelWithCornersSelf_prod] at hΦ
  obtain ⟨V, hDV, J, hJformula, hJ⟩ :=
    exists_uniform_projectedFlow_embedding_neighborhood D (lgManifold n) j Φ hΦ htime
  refine ⟨D, j, Φ, V, hDV, J, himage, hDimage, hDne, hJformula, hJ, ?_⟩
  intro t
  have hforward (x : V) (hx : x.val ∈ D.carrier) :
      tailoringFamily I β t.val ((J t).map x) = 1 ∧
        φ ((J t).map x).1 ≤ A ∧
        (φ ((J t).map x).1 = A ↔ φ (j.map x.val).1 = A) := by
    have hxφ : φ (j.map x.val).1 ≤ A := by rwa [hcarrier] at hx
    have h := hpres (0, j.map x.val) hzero (hbase x.val) hxφ t.val
      (by simpa only [zero_add] using t.property)
    rw [hJformula]
    refine ⟨?_, h.2.2.1, h.2.2.2.1⟩
    have htime' : (Φ t.val (0, j.map x.val)).1 = t.val := by
      simpa only [zero_add] using h.1
    rw [htime'] at h
    exact h.2.1
  have hback (y : LGSpace n) (hy : tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A) :
      ∃ x : V, x.val ∈ D.carrier ∧ (J t).map x = y ∧
        (φ (j.map x.val).1 = A ↔ φ y.1 = A) := by
    have h := hpres (t.val, y) t.property hy.1 hy.2 (-t.val)
      (by simpa only [add_neg_cancel] using hzero)
    have ht0 : (Φ (-t.val) (t.val, y)).1 = 0 := by simpa only [add_neg_cancel] using h.1
    have hy0 : tailoringFamily I β 0 (Φ (-t.val) (t.val, y)).2 = 1 ∧
        φ (Φ (-t.val) (t.val, y)).2.1 ≤ A := by
      exact ⟨by simpa only [ht0] using h.2.1, h.2.2.1⟩
    have hm : (Φ (-t.val) (t.val, y)).2 ∈ j.map '' D.carrier := by rwa [hDimage]
    obtain ⟨z, hz, heq⟩ := hm
    let x : V := ⟨z, hDV hz⟩
    have hp : (0, j.map z) = Φ (-t.val) (t.val, y) := Prod.ext ht0.symm heq
    refine ⟨x, hz, ?_, ?_⟩
    · rw [hJformula]
      change (Φ t.val (0, j.map z)).2 = y
      rw [hp, ← Φ.map_add, add_neg_cancel, Flow.map_zero_apply]
    · simpa only [x, heq] using h.2.2.2.1
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hforward x hx).1, (hforward x hx).2.1⟩
    · intro hy
      obtain ⟨x, hx, heq, _⟩ := hback y hy
      exact ⟨x, hx, heq⟩
  · rw [D.frontier_restrict_carrier V]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxA : φ (j.map x.val).1 = A := by rwa [hfrontier] at hx
      have hxD : x.val ∈ D.carrier := D.compact.isClosed.frontier_subset hx
      exact ⟨(hforward x hxD).1, (hforward x hxD).2.2.mpr hxA⟩
    · intro hy
      obtain ⟨x, hx, heq, hboundary⟩ := hback y ⟨hy.1, hy.2.le⟩
      refine ⟨x, ?_, heq⟩
      change x.val ∈ frontier D.carrier
      rw [hfrontier]
      exact hboundary.mpr hy.2

end FsFltz
