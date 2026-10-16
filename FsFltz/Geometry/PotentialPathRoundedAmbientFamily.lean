import FsFltz.Geometry.PotentialPathPrimitiveFamily
import FsFltz.Geometry.PotentialPathRoundedOutward
import FsFltz.Geometry.CompactDomainLiouvillePullback

/-!
# Liouville families on retained holomorphic rounded carriers

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and assembly, lines 2148–2158. Actual finite-input outwardness constructs
the structures on the supplied transported carrier and embeddings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry
open SmoothManifold
variable {n : ℕ}

local instance pathAmbientCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- The prescribed path constructs actual Liouville structures on every
retained ambient presentation with the literal rounded carrier and frontier
images. Nondegeneracy and outwardness follow from the potential estimates. -/
theorem ToricInput.coefficientPath_potentialPath_rounded_embedded_liouvilleFamily
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    let hφE := hφ.comp (EuclideanSpace.equiv (Fin n) ℝ).contDiff
    ∃ A₀ R₀ : ℝ, 0 < A₀ ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ Kstar : ℝ, 0 < Kstar ∧
      coefficientPotentialPathThreshold I hφE hc hlower R ≤ Kstar ∧
      ∀ A : ℝ, 2 * A₀ ≤ A → ∀ Aminus : ℝ, Aminus < A →
      ∃ δ : ℝ, 0 < δ ∧ δ < A - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ (E : CompactDomain (2 * n))
        (J : Parameter → E.extension.SmoothEmbedding (lgManifold n)),
      E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) →
      (∀ t, (J t).map '' E.carrier =
        {y | potentialPath_roundedDefiningFunction I φ R A m (t.val, y) ≤ 0}) →
      (∀ t, (J t).map '' frontier E.carrier =
        {y | potentialPath_roundedDefiningFunction I φ R A m (t.val, y) = 0}) →
      ∀ K : ℝ, Kstar ≤ K →
      ∃ Λ : Parameter → LiouvilleStructure E,
        (∀ t, (Λ t).primitive = E.extension.pullback (lgManifold n) (J t).map
          ((lgManifold n).rankTwoPrimitive
            (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
            (W (I.alongCoefficientPath t.val)) K)) ∧
        E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) ∧
        E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) ∧
        (∀ t, E.extension.IsSymplecticOn (E.extension.exteriorDerivative (Λ t).primitive) univ) ∧
        Nonempty (LocalizedCompletionFamily E Λ) := by
  obtain ⟨A₀, R₀, hA₀, hR₀, hout⟩ :=
    FsFltz.Geometry.ToricInput.coefficientPath_potentialPath_rounded_outward I hφ hc hlower hupper hEnd hhom hL hend
  refine ⟨A₀, R₀, hA₀, hR₀, ?_⟩
  intro R hR
  obtain ⟨Kstar, hKstar, hKpath, hout⟩ := hout R hR
  refine ⟨Kstar, hKstar, hKpath, ?_⟩
  intro A hA Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout A hA Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd E J hJ hcarrier hfront K hK
  let α : Parameter → (lgManifold n).Form 1 := fun t =>
    (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t.val))
      (W (I.alongCoefficientPath t.val)) K
  have hα : (lgManifold n).IsSmoothIntervalFormFamily α :=
    ⟨fun t => (lgManifold n).rankTwoPrimitive
      (lambdaPotentialForm (potentialPath (fun u => realSquaredNorm u / 2) φ t))
      (W (I.alongCoefficientPath t)) K,
      isSmoothFormFamily_coefficientPath_potentialPath_primitive I hφ K, fun _ => rfl⟩
  have hnd (t : Parameter) (y : (lgManifold n).Point) :
      (lgManifold n).Nondegenerate ((lgManifold n).exteriorDerivative (α t)) y :=
    (isSymplecticOn_potential_W_ambient (potentialPath_native_contDiff hφ t.val)
      (lt_min zero_lt_one hc) (potentialPath_native_hessian_lowerBound hφ hlower t.property)
      (I.alongCoefficientPath t.val) (hKstar.le.trans hK)).2.2 y (mem_univ _)
  let q : Parameter → LGSpace n → ℝ := fun t y =>
    potentialPath_roundedDefiningFunction I φ R A m (t.val, y)
  have hq (t : Parameter) :
      ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ (q t) :=
    (contMDiff_potentialPath_roundedDefiningFunction_joint I hφ R A m).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hside (t : Parameter) (x : E.extension.Point) (hx : x ∈ E.carrier) :
      q t ((J t).map x) ≤ 0 := by
    have hy : (J t).map x ∈ (J t).map '' E.carrier := ⟨x, hx, rfl⟩
    rw [hcarrier t] at hy
    exact hy
  have hzero (t : Parameter) (x : E.extension.Point) (hx : x ∈ frontier E.carrier) :
      q t ((J t).map x) = 0 := by
    have hy : (J t).map x ∈ (J t).map '' frontier E.carrier := ⟨x, hx, rfl⟩
    rw [hfront t] at hy
    exact hy
  obtain ⟨Λ, hprim, hforms, hfields, hsymp, hcompletion, _⟩ :=
    E.exists_liouvilleFamily_of_sublevel_pullback (lgManifold n) J hJ α hα hnd q hq
      hside hzero (fun t x hx =>
        hout m hm hmd K hK t.val t.property ((J t).map x) (hzero t x hx).ge)
  exact ⟨Λ, hprim, hforms, hfields, hsymp, hcompletion⟩

end FsFltz.Geometry
