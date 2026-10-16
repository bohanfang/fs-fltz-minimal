import FsFltz.Geometry.TailoringFlowEmbedding
import FsFltz.Geometry.CompactCarrierTangentKernel
import FsFltz.Geometry.FamilyPullback
import FsFltz.Geometry.IntrinsicLiouvilleFamilyExtension

/-!
# Actual primitive family on the transported fixed tailoring carrier

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–1009,
and `subsec:fiberends`, lines 1208–1237. The literal equation on the
constructed compact carrier determines the transported tangent kernel.
Its actual pulled-back primitive is jointly smooth and symplectic on
one common open neighborhood. Ambient rounding, outwardness and pair
completion assembly are separate producers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}

/-- One nonempty fixed native tailoring carrier carries the actual jointly
smooth pullback primitive family. Its tangent kernel is proved from the
literal fiber image, and symplecticity holds on one common open extension
neighborhood for every interval parameter. No tangent or symplectic family
certificate is supplied in the inputs. -/
theorem tailoringFamily_exists_uniform_fixedCarrier_primitiveFamily
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
      ∃ (D : CompactDomain (2 * n - 2))
        (J : Parameter → D.extension.SmoothEmbedding (lgManifold n))
        (O : TopologicalSpace.Opens D.extension.Point),
        D.carrier.Nonempty ∧ D.carrier ⊆ O ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        (∀ t : Parameter,
          (J t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
          (J t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A}) ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker) ∧
        D.extension.IsSmoothIntervalFormFamily
          (fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) ∧
        ∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative
            (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ))) O := by
  obtain ⟨F, hF, B, hB, hcarrier⟩ := tailoringFamily_exists_uniform_fixedCarrier_embeddings
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  obtain ⟨_d, _hd, _R, _hR, Bπ, _hBπ, hπ⟩ :=
    tailoringFamily_exists_uniform_native_planePairing_positivity I hφ hc hU hlower hupper
  refine ⟨F, hF, max B Bπ, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ A hA
  have hβcarrier : B ≤ β := (le_max_left _ _).trans hβ
  have hβπ : Bπ ≤ β := (le_max_right _ _).trans hβ
  obtain ⟨D₀, _j, _Φ, V, hD₀V, J, _hbase, _hbaseImage, hD₀ne,
    _hformula, hJ, himages⟩ := hcarrier β hβcarrier A hA
  let D := D₀.restrict V hD₀V
  have hDne : D.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hD₀ne
    exact ⟨⟨x, hD₀V hx⟩, hx⟩
  have hlevel : ∀ t : Parameter, ∀ x ∈ D.carrier,
      tailoringFamily I β t.val ((J t).map x) = 1 := by
    intro t x hx
    have hm : (J t).map x ∈ (J t).map '' D.carrier := ⟨x, hx, rfl⟩
    rw [(himages t).1] at hm
    exact hm.1
  have hreg : ∀ t : Parameter, ∀ y, tailoringFamily I β t.val y = 1 →
      Function.Surjective (complexDifferential (lgManifold n) (tailoringFamily I β t.val) y) := by
    intro t y hy
    have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower y
    apply (lgManifold n).complexDifferential_surjective_of_planePairing_ne_zero
      (lambdaPotentialForm φ) (tailoringFamily I β t.val) y hnd
    exact ((hπ β hβπ t.val t.property y hnd).2.2 (by
      simp only [hy, norm_one, le_refl])).ne'
  have hkernel : ∀ t : Parameter, ∀ x ∈ D.carrier,
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
        (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker := by
    intro t
    have h := compactCarrier_embedding_tangent_range (d := 2 * n) (F := ℂ)
    rw [Complex.finrank_real_complex] at h
    exact h D (lgManifold n) (J t) (tailoringFamily I β t.val) 1
      (contMDiff_tailoringFamily_lgManifold I β t.val) (hreg t) (hlevel t)
  let μ : Parameter → D.extension.Form 1 :=
    fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)
  have hα : (lgManifold n).IsSmoothIntervalFormFamily (fun _ : Parameter => lambdaPotentialForm φ) := by
    refine ⟨fun _ => lambdaPotentialForm φ, ?_, fun _ => rfl⟩
    intro a
    refine ⟨univ ×ˢ (chartAt (Model (2 * n)) a).target,
      isOpen_univ.prod (chartAt (Model (2 * n)) a).open_target,
      prod_mono (subset_univ _) Subset.rfl, ?_⟩
    exact ((isSmoothForm_lambdaPotentialForm hφ) a).comp contDiffOn_snd (fun _ hp => hp.2)
  have hμ : D.extension.IsSmoothIntervalFormFamily μ :=
    D.extension.isSmoothIntervalFormFamily_pullback_one (lgManifold n)
      (fun t => (J t).map) hJ (fun _ => lambdaPotentialForm φ) hα
  have hnd : ∀ t : Parameter, ∀ x ∈ D.carrier,
      D.extension.Nondegenerate (D.extension.exteriorDerivative (μ t)) x := by
    intro t x hx
    have hnd := nondegenerate_lambdaPotentialForm_of_lowerBound hφ hc hlower ((J t).map x)
    apply (lgManifold n).nondegenerate_pullback_of_rankTwo_kernel D.extension (J t)
      (lambdaPotentialForm φ) (isSmoothForm_lambdaPotentialForm hφ) x hnd
      (Complex.reCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)))
      (Complex.imCLM.comp (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)))
      ((hπ β hβπ t.val t.property ((J t).map x) hnd).2.2 (by
        simp only [hlevel t x hx, norm_one, le_refl])).ne'
    rw [← (lgManifold n).complexDifferential_ker_eq_real_inf_imag]
    exact hkernel t x hx
  obtain ⟨O, hDO, hndO⟩ := D.exists_common_symplecticNeighborhood_of_primitiveFamily μ hμ hnd
  refine ⟨D, J, O, hDne, hDO, hJ, ?_, hkernel, hμ, ?_⟩
  · intro t
    exact himages t
  · intro t
    apply (D.extension.isSymplecticOn_exteriorDerivative_iff (μ t)
      (D.extension.isSmoothForm_of_isSmoothIntervalFormFamily μ hμ t) O).mpr
    exact hndO t

end FsFltz
