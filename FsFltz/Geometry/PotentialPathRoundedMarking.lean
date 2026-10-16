import FsFltz.Geometry.PotentialPathRoundedPairFamily
import FsFltz.Geometry.PotentialAmbientPath
import FsFltz.Geometry.TailoringRoundedMarkingFamilyTransfer
import FsFltz.Geometry.CommonEmbeddingCompactMap

/-!
# Inclusion markings of the retained holomorphic rounded presentations

Source: `geometric-part-fsf-proof.tex`, `lem:absorption`, lines 444–468,
`lem:markedfamily`, lines 975–1049, and assembly, lines 2148–2158.
Actual rounded outwardness and complete native flow produce markings on
any supplied genuine compact presentation and its chosen completion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set
namespace FsFltz.Geometry
open SmoothManifold

/-- A literal embedded absorbing sublevel marks every completion of the
retained source domain, with exactly the supplied compact inclusion. -/
theorem Completion.exists_inclusionMarking_of_embedded_absorbing_sublevel
    {d : ℕ} {S : LiouvilleDomain d} (C : Completion S)
    (hS : S.domain.carrier.Nonempty) (P : CompleteLiouvilleManifold d)
    (q : P.manifold.Point → ℝ)
    (hq : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ q)
    (hcompact : IsCompact {x | q x ≤ 0})
    (hout : ∀ x, q x = 0 →
      0 < P.manifold.scalarDerivative q x (P.manifold.liouvilleVector P.primitive x))
    (habsorb : ∀ x, ∃ T : ℝ, 0 ≤ T ∧ q (P.completeFlow.flow (-T) x) ≤ 0)
    (j : S.domain.extension.SmoothEmbedding P.manifold)
    (himage : j.map '' S.domain.carrier = {x | q x ≤ 0})
    (hp : ∀ x ∈ S.domain.carrier,
      S.liouville.primitive x = S.domain.extension.pullback P.manifold j.map P.primitive x) :
    Nonempty (InclusionMarking C P (fun x => j.map x.val)) := by
  let B := regularSublevelLiouvilleDomain P.manifold q hq hcompact P.primitive
    P.smooth_primitive P.symplectic hout
  let k := SmoothEmbedding.identity P.manifold
  have himage' : j.map '' S.domain.carrier = k.map '' B.domain.carrier := by
    change j.map '' S.domain.carrier = id '' {x | q x ≤ 0}
    simpa using himage
  obtain ⟨h, hsquare, _⟩ := S.domain.exists_compactDiffeomorph_of_commonEmbedding
    B.domain P.manifold hS j k himage'
  have hprim : ∀ x ∈ S.domain.carrier,
      S.domain.extension.pullback P.manifold h.map P.primitive x = S.liouville.primitive x := by
    intro x hx
    rw [hp x hx]
    have he := h.pullback_of_commonEmbedding P.manifold j k hsquare P.primitive x hx
    change S.domain.extension.pullback P.manifold h.map
      (P.manifold.pullback P.manifold id P.primitive) x = _ at he
    rw [P.manifold.pullback_id] at he
    exact he
  obtain ⟨Q, _⟩ := C.exists_inclusionMarking_of_absorbing_sublevel P q hq hcompact hout habsorb h hprim
  have heq : (fun x : S.domain.Point => h.map x.val) = (fun x => j.map x.val) := by
    funext x
    exact hsquare x.val (h.contains_source x.property)
  rw [heq] at Q
  exact ⟨Q⟩

variable {n : ℕ}
local instance pathMarkingCharts : ChartedSpace (Model (2 * n)) (LGSpace n) :=
  (lgManifold n).charts

/-- Actual holomorphic rounded outwardness produces inclusion markings on
all retained presentations and all their completions. -/
theorem ToricInput.coefficientPath_potentialPath_exists_rounded_ambient_markings
    (I : ToricInput n) {φ φEnd : RealSpace n → ℝ} {c U : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    (hupper : ∀ u v : EuclideanSpace ℝ (Fin n),
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2)
    (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u) :
    ∃ A₀ R₀ : ℝ, 0 < A₀ ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∃ Kstar : ℝ, 0 < Kstar ∧
      ∀ A : ℝ, 2 * A₀ ≤ A → ∀ Aminus : ℝ, Aminus < A →
      ∃ δ : ℝ, 0 < δ ∧ δ < A - Aminus ∧
      ∀ m : RoundingChoice, 0 < m.eps → m.eps ≤ δ →
      ∀ K : ℝ, Kstar ≤ K → ∃ hK : 0 ≤ K, ∀ t : Parameter,
      let P := (potentialPath_W_ambientCompletePrimitive hφ hEnd1 hEnd hhom hc
        hlower hupper hL hend t.val t.property (I.alongCoefficientPath t.val) hK).toCompleteLiouvilleManifold
      ∀ (S : LiouvilleDomain (2 * n)) (C : Completion S), S.domain.carrier.Nonempty →
      ∀ j : S.domain.extension.SmoothEmbedding (lgManifold n),
      j.map '' S.domain.carrier = {y | potentialPath_roundedDefiningFunction I φ R A m (t.val, y) ≤ 0} →
      (∀ x ∈ S.domain.carrier, S.liouville.primitive x =
        S.domain.extension.pullback (lgManifold n) j.map P.primitive x) →
      Nonempty (InclusionMarking C P (fun x => j.map x.val)) := by
  obtain ⟨A₀, R₀, hA₀, hR₀, hout⟩ := ToricInput.coefficientPath_potentialPath_rounded_outward
    I hφ hc hlower hupper hEnd hhom hL hend
  refine ⟨A₀, R₀, hA₀, hR₀, ?_⟩
  intro R hR
  obtain ⟨Kstar, hKstar, _hKpath, hout⟩ := hout R hR
  refine ⟨Kstar, hKstar, ?_⟩
  intro A hA Aminus hgap
  obtain ⟨δ, hδ, hδgap, hout⟩ := hout A hA Aminus hgap
  refine ⟨δ, hδ, hδgap, ?_⟩
  intro m hm hmd K hK
  have hK0 : 0 ≤ K := hKstar.le.trans hK
  refine ⟨hK0, ?_⟩
  intro t P S C hS j himage hp
  let q : (lgManifold n).Point → ℝ := fun y =>
    potentialPath_roundedDefiningFunction I φ R A m (t.val, y)
  have hq : ContMDiff 𝓘(ℝ, Model (2 * n)) 𝓘(ℝ, ℝ) ∞ q :=
    (contMDiff_potentialPath_roundedDefiningFunction_joint I hφ R A m).comp
      (contMDiff_const.prodMk contMDiff_id)
  have hcompact (a : ℝ) : IsCompact {y | q y ≤ a} := by
    apply (isCompact_potential_sublevel (potentialPath_native_contDiff hφ t.val)
      (potentialPath_native_end_contDiff hEnd1 t.val)
      (potentialPath_native_end_contDiffAt hEnd t.val)
      (potentialPath_native_end_homogeneous hhom t.val) (lt_min zero_lt_one hc)
      (potentialPath_native_hessian_lowerBound hφ hlower t.property) hL
      (potentialPath_native_eq_end hend t.val) (a + A)).of_isClosed_subset
      (isClosed_le hq.continuous continuous_const)
    intro y hy
    have hl := (le_max_left
      (potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 - A)
      (Complex.normSq (W (I.alongCoefficientPath t.val) y) - R ^ 2)).trans
        ((m.profile.lower _).trans hy)
    change potentialPath (fun u => realSquaredNorm u / 2) φ t.val y.1 ≤ a + A
    linarith
  have hpos : ∀ y, 0 ≤ q y → 0 < P.manifold.scalarDerivative q y (P.field y) :=
    fun y hy => hout m hm hmd K hK t.val t.property y hy
  have habsorb : ∀ y, ∃ T : ℝ, 0 ≤ T ∧ q (P.completeFlow.flow (-T) y) ≤ 0 := by
    intro y
    exact P.completeFlow.exists_nonneg_time_scalar_le q hq P.smooth_field hcompact 0 hpos y
  exact C.exists_inclusionMarking_of_embedded_absorbing_sublevel hS P q hq (hcompact 0)
    (fun y hy => by rw [← P.field_eq_liouvilleVector]; exact hpos y hy.ge)
    habsorb j himage hp
end FsFltz.Geometry
