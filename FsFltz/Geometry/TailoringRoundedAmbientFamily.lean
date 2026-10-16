import FsFltz.Geometry.TailoringRoundedPairCarrier
import FsFltz.Geometry.CompactDomainLiouvillePullback
import FsFltz.Geometry.TailoringPotentialDomainFamily

/-!
# Actual Liouville families on the common rounded ambient carrier

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and marked deformation, lines 1239–1326. The same fixed ambient and ribbon
presentations are retained. One coefficient threshold produces all actual
pulled-back ambient Liouville structures and their localized completions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz
open Geometry
variable {n : ℕ}

/-- The actual compatible rounded pair presentations support the smooth
ambient Liouville family for every coefficient above one uniform threshold.
All structures use the same embeddings and fixed carriers, including the
entire native boundary embedding of the fixed ribbon. -/
theorem tailoringFamily_exists_uniform_rounded_ambient_liouvilleFamily
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
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β ≥ β₀,
      ∃ Kstar : ℝ, 0 < Kstar ∧ ∀ R : ℝ, 0 < R →
      ∀ Aminus : ℝ, F ^ 2 * β ^ 2 / 2 ≤ Aminus → Aminus < Cplus ^ 2 * β ^ 2 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < Cplus ^ 2 * β ^ 2 / 2 - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∃ (E : CompactDomain (2 * n)) (D : CompactDomain (2 * n - 2))
        (χ : E.extension.SmoothEmbedding (lgManifold n))
        (i : D.extension.SmoothEmbedding E.extension)
        (k : D.extension.SmoothEmbedding E.boundary)
        (Φ : Flow ℝ (ℝ × LGSpace n))
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n))
        (Λ : (K : ℝ) → Kstar ≤ K → Parameter → LiouvilleStructure E),
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
        (∀ t : Parameter,
          (J t).map '' E.carrier = tailoringRoundedDomain I φ β t.val R
            (Cplus ^ 2 * β ^ 2 / 2) m ∧
          (J t).map '' frontier E.carrier =
            {y | tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m y = 0} ∧
          ((J t).comp i).map '' D.carrier =
            {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ Aminus} ∧
          ((J t).comp i).map '' frontier D.carrier =
            {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = Aminus} ) ∧
        (∀ K hK t, (Λ K hK t).primitive = E.extension.pullback (lgManifold n) (J t).map
          ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K)) ∧
        ∀ K hK,
          E.extension.IsSmoothIntervalFormFamily (fun t => (Λ K hK t).primitive) ∧
          E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ K hK t).field) ∧
          (∀ t, E.extension.IsSymplecticOn (E.extension.exteriorDerivative (Λ K hK t).primitive) univ) ∧
          Nonempty (LocalizedCompletionFamily E (Λ K hK))
 := by
  classical
  obtain ⟨F, hF, hcarrier⟩ := tailoringFamily_exists_uniform_rounded_fixedPair_carriers
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨Bs, _hBs, hsym⟩ := tailoringFamily_exists_uniform_symplectic I hφ hc hU hlower hupper
  refine ⟨F, hF, ?_⟩
  intro Cplus hCF
  obtain ⟨Bc, hBc, hcarrier⟩ := hcarrier Cplus hCF
  obtain ⟨Bo, _hBo, hout⟩ := tailoringFamily_exists_uniform_rounded_outwardness
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend (hF.trans hCF)
  let β₀ := max Bc (max Bs Bo)
  refine ⟨β₀, hBc.trans_le (le_max_left _ _), ?_⟩
  intro β hβ
  have hβc : Bc ≤ β := (le_max_left _ _).trans hβ
  have hβs : Bs ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβo : Bo ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  obtain ⟨Kstar, hKstar, hout⟩ := hout β hβo
  refine ⟨Kstar, hKstar, ?_⟩
  intro R hR Aminus hlo hhi
  obtain ⟨δc, hδc, hgapc, hcarrier⟩ := hcarrier β hβc R hR Aminus hlo hhi
  obtain ⟨δo, hδo, _hgapo, hout⟩ := hout R hR Aminus hhi
  refine ⟨min δc δo, lt_min hδc hδo, (min_le_left _ _).trans_lt hgapc, ?_⟩
  intro m hm hmd
  have hmdc := hmd.trans (min_le_left δc δo)
  have hmdo := hmd.trans (min_le_right δc δo)
  obtain ⟨E, D, χ, i, k, Φ, J, hEne, hDne, hrange, hk, hχ, hχfront, hJzero,
    hJflow, hJ, hRj, himages⟩ := hcarrier m hm hmdc
  let α : ℝ → Parameter → (lgManifold n).Form 1 := fun K t =>
    (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β t.val) K
  let q : Parameter → LGSpace n → ℝ := fun t =>
    tailoringRoundedDefiningFunction I φ β t.val R (Cplus ^ 2 * β ^ 2 / 2) m
  have hside : ∀ t x, x ∈ E.carrier → q t ((J t).map x) ≤ 0 := by
    intro t x hx
    have hy : (J t).map x ∈ (J t).map '' E.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).1] at hy
    exact hy
  have hzero : ∀ t x, x ∈ frontier E.carrier → q t ((J t).map x) = 0 := by
    intro t x hx
    have hy : (J t).map x ∈ (J t).map '' frontier E.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).2.1] at hy
    exact hy
  have hfamily (K : ℝ) (hK : Kstar ≤ K) := E.exists_liouvilleFamily_of_sublevel_pullback
    (lgManifold n) J hJ (α K)
    (show (lgManifold n).IsSmoothIntervalFormFamily (α K) from
      ⟨fun s => (lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ) (tailoringFamily I β s) K,
        isSmoothFormFamily_tailoringPrimitive I β K hφ, fun _ => rfl⟩)
    (fun t y => (hsym β hβs t.val t.property K (hKstar.le.trans hK)).2.2 y (mem_univ _))
    q (fun t => contMDiff_tailoringRoundedDefiningFunction I hφ β t.val R
      (Cplus ^ 2 * β ^ 2 / 2) m) hside hzero
    (fun t x hx => hout m hm hmdo K hK t.val t.property ((J t).map x)
      (tailoringRoundedDomain_subset I φ β t.val (Cplus ^ 2 * β ^ 2 / 2) hR m
        (show (J t).map x ∈ tailoringRoundedDomain I φ β t.val R
          (Cplus ^ 2 * β ^ 2 / 2) m from (hzero t x hx).le)).1 (hzero t x hx).ge)
  choose Λ hprim hforms hfields hsymp hcompletion _hmap using hfamily
  exact ⟨E, D, χ, i, k, Φ, J, Λ, hEne, hDne, hrange, hk, hχ, hχfront, hJzero,
    hJflow, hJ, hRj, himages, hprim, fun K hK =>
      ⟨hforms K hK, hfields K hK, hsymp K hK, hcompletion K hK⟩⟩

end FsFltz
