import FsFltz.Geometry.TailoringRibbonOutward
import FsFltz.Geometry.PairFamilyConstruction

/-!
# The actual fixed tailoring ribbon Liouville and completion family

Source: `geoemtric-part-fsf.tex`, `def:chain`, lines 163–169;
`geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and `eq:fiberends`, lines 1208–1237. Restricting the same transported
carrier to its common symplectic neighborhood constructs its actual
Liouville structures and localized completion family. Both entire image
equations and the exact pulled-back primitive remain literal. Ambient
pair compatibility and inclusion markings are separate producers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.SmoothManifold

/-- A plane-primitive update vanishes on an embedded tangent space in the
kernel of the actual complex differential. Thus the ambient primitive
restricts to the intrinsic ribbon primitive for every real coefficient. -/
theorem pullback_rankTwoPrimitive_eq_of_tangent_range_le_kernel {d e : ℕ}
    (N : SmoothManifold d) (M : SmoothManifold e) (j : N.SmoothEmbedding M)
    (α : M.Form 1) (f : M.Point → ℂ) (K : ℝ) (x : N.Point)
    (hkernel : (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x).range ≤
      (complexDifferential M f (j.map x)).ker) :
    N.pullback M j.map (M.rankTwoPrimitive α f K) x = N.pullback M j.map α x := by
  ext vs
  have hv : (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs i)) =
      fun _ : Fin 1 => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs 0) := by
    funext i
    rw [Fin.eq_zero i]
  simp only [pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change (M.rankTwoPrimitive α f K (j.map x))
    (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs i)) =
      (α (j.map x)) (fun i => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs i))
  rw [hv]
  change evalOne (M.rankTwoPrimitive α f K) (j.map x)
    (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs 0)) =
      evalOne α (j.map x) (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs 0))
  have hdf : complexDifferential M f (j.map x)
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model e) j.map x (vs 0)) = 0 :=
    hkernel ⟨vs 0, rfl⟩
  rw [M.evalOne_rankTwoPrimitive, hdf]
  simp

end FsFltz.Geometry.SmoothManifold

namespace FsFltz
open Geometry Geometry.SmoothManifold

variable {n : ℕ}

/-- The actual tailoring ribbon family on one nonempty fixed carrier has
its literal pullback primitives, jointly smooth canonical fields and a
constructed compatible localized completion family. All Liouville and
completion data are outputs of finite toric/potential inputs; no geometric
family certificate is assumed. -/
theorem tailoringFamily_exists_uniform_fixedCarrier_liouvilleFamily
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
        (Λ : Parameter → LiouvilleStructure D),
        D.carrier.Nonempty ∧
        D.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (J t).map) ∧
        (∀ t : Parameter,
          (J t).map '' D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 ≤ A} ∧
          (J t).map '' frontier D.carrier = {y | tailoringFamily I β t.val y = 1 ∧ φ y.1 = A}) ∧
        (∀ t x, x ∈ D.carrier →
          (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (J t).map x).range =
            (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((J t).map x)).ker) ∧
        (∀ t, (Λ t).primitive =
          D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) ∧
        D.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) ∧
        D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) ∧
        (∀ t : Parameter, D.extension.IsSymplecticOn
          (D.extension.exteriorDerivative (Λ t).primitive) univ) ∧
        Nonempty (LocalizedCompletionFamily D Λ) ∧
        ∀ (t : Parameter) (K : ℝ) (x : D.extension.Point), x ∈ D.carrier →
          D.extension.pullback (lgManifold n) (J t).map
            ((lgManifold n).rankTwoPrimitive (lambdaPotentialForm φ)
              (tailoringFamily I β t.val) K) x = (Λ t).primitive x := by
  obtain ⟨F, hF, β₀, hβ₀, hfamily⟩ :=
    tailoringFamily_exists_uniform_fixedCarrier_outwardPrimitiveFamily
      I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ A hA
  obtain ⟨D, J, O, hDne, hDO, hJ, himages, hkernel, hμ, hsymplectic, hout⟩ :=
    hfamily β hβ A hA
  let E := D.restrict O hDO
  let μ : Parameter → D.extension.Form 1 :=
    fun t => D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)
  let μ' : Parameter → E.extension.Form 1 :=
    fun t => E.extension.pullback D.extension Subtype.val (μ t)
  have hsm (t : Parameter) : D.extension.IsSmoothForm (μ t) :=
    D.extension.isSmoothForm_of_isSmoothIntervalFormFamily μ hμ t
  have hsm' (t : Parameter) : E.extension.IsSmoothForm (μ' t) :=
    E.extension.isSmoothForm_pullback_one D.extension
      (D.extension.restrictInclusion O).map (μ t) (hsm t)
  have hnd' (t : Parameter) (x : E.extension.Point) :
      E.extension.Nondegenerate (E.extension.exteriorDerivative (μ' t)) x := by
    intro v hv
    apply (hsymplectic t).2.2 x.val x.property v
    intro w
    have heq := hv w
    unfold evalTwo at heq ⊢
    rw [D.extension.exteriorDerivative_restrict O (μ t) (hsm t) x] at heq
    exact heq
  have hglobal (t : Parameter) : E.extension.IsSymplecticOn
      (E.extension.exteriorDerivative (μ' t)) univ :=
    (E.extension.isSymplecticOn_exteriorDerivative_iff _ (hsm' t) _).mpr
      (fun x _ => hnd' t x)
  have hfield (t : Parameter) (x : E.extension.Point) :
      E.extension.liouvilleVector (μ' t) x = D.extension.liouvilleVector (μ t) x.val := by
    apply E.extension.liouvilleVector_eq (μ' t) x (hnd' t x)
    intro v
    dsimp only [μ']
    unfold evalTwo evalOne
    erw [D.extension.exteriorDerivative_restrict O (μ t) (hsm t) x,
      D.extension.pullback_restrict_val O (μ t) x]
    exact D.extension.liouvilleVector_contraction (μ t) x.val
      (D.extension.liouvilleEquation_exists (μ t) x.val
        ((hsymplectic t).2.2 x.val x.property)) v
  let Λ : Parameter → LiouvilleStructure E := fun t =>
    { primitive := μ' t
      smooth_primitive := hsm' t
      symplectic := ⟨(hglobal t).1, fun x _ => (hglobal t).2.1 x (mem_univ _),
        fun x _ => (hglobal t).2.2 x (mem_univ _)⟩
      field := E.extension.liouvilleVector (μ' t)
      smooth_field := E.extension.isSmoothVectorField_liouvilleVector _ (hsm' t) (hnd' t)
      contraction := fun x _ => E.extension.liouvilleVector_contraction _ x
        (E.extension.liouvilleEquation_exists _ x (hnd' t x))
      outward := by
        intro x hx
        have hx' : x.val ∈ frontier D.carrier := by
          rw [D.frontier_restrict_carrier O] at hx
          exact hx
        let B := D.defining x.val hx'
        have hρ := (B.smooth_rho.contMDiffAt
          (B.open_neighbourhood.mem_nhds B.mem_neighbourhood)).mdifferentiableAt (by simp)
        change (0 : ℝ) < (show ℝ from mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, ℝ)
          (fun y : O => B.rho y.val) x (E.extension.liouvilleVector (μ' t) x))
        rw [hfield t x]
        have hchain := mfderiv_comp (f := (Subtype.val : O → D.extension.Point))
          (g := B.rho) x hρ
          ((D.extension.restrictInclusion O).map.contMDiff.mdifferentiableAt (by simp))
        erw [D.extension.mfderiv_restrict_val O x] at hchain
        exact (congrArg (fun T => (T (D.extension.liouvilleVector (μ t) x.val) : ℝ))
          hchain).trans_gt (hout t x.val hx') }
  let K : Parameter → E.extension.SmoothEmbedding (lgManifold n) := fun t =>
    { map := ⟨fun x => (J t).map x.val,
        (J t).map.contMDiff.comp (D.extension.restrictInclusion O).map.contMDiff⟩
      embedding := (J t).embedding.comp Topology.IsEmbedding.subtypeVal
      immersion := by
        intro x
        change Function.Injective (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
          (fun y : O => (J t).map y.val) x)
        rw [D.extension.mfderiv_comp_restrict_val (lgManifold n) O x
          ((J t).map.contMDiff.mdifferentiableAt (by simp))]
        exact (J t).immersion x.val }
  have hK : E.extension.IsSmoothIntervalMapFamily (lgManifold n) (fun t => (K t).map) :=
    E.extension.isSmoothIntervalMapFamily_comp_of_contMDiff_family D.extension (lgManifold n)
      (fun t => (J t).map) hJ (fun _ x => x.val)
      (contMDiff_subtype_val.comp contMDiff_snd)
  have hKkernel : ∀ t x, x ∈ E.carrier →
      (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) (K t).map x).range =
        (complexDifferential (lgManifold n) (tailoringFamily I β t.val) ((K t).map x)).ker := by
    intro t x hx
    change (mfderiv 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n))
      (fun y : O => (J t).map y.val) x).range = _
    rw [D.extension.mfderiv_comp_restrict_val (lgManifold n) O x
      ((J t).map.contMDiff.mdifferentiableAt (by simp))]
    exact hkernel t x.val hx
  have hprimitive (t : Parameter) : (Λ t).primitive =
      E.extension.pullback (lgManifold n) (K t).map (lambdaPotentialForm φ) := by
    change E.extension.pullback D.extension Subtype.val
      (D.extension.pullback (lgManifold n) (J t).map (lambdaPotentialForm φ)) = _
    exact (E.extension.pullback_comp D.extension (lgManifold n)
      (u := (Subtype.val : O → D.extension.Point)) (v := (J t).map)
      ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).mdifferentiable (by simp))
      ((J t).map.contMDiff.mdifferentiable (by simp)) (lambdaPotentialForm φ)).symm
  have hΛ : E.extension.IsSmoothIntervalFormFamily (fun t => (Λ t).primitive) :=
    E.extension.isSmoothIntervalFormFamily_pullback_one_of_contMDiff_family D.extension
      (fun _ x => x.val) (contMDiff_subtype_val.comp contMDiff_snd) μ hμ
  have hΛfield : E.extension.IsSmoothIntervalVectorFieldFamily (fun t => (Λ t).field) :=
    E.extension.isSmoothIntervalVectorFieldFamily_liouvilleVector μ' hΛ hnd'
  refine ⟨E, K, Λ, ?_, hK, ?_, hKkernel, hprimitive, hΛ, hΛfield, hglobal,
    E.exists_smooth_localizedCompletionFamily_of_liouvilleFamily Λ hΛ, ?_⟩
  · obtain ⟨x, hx⟩ := hDne
    exact ⟨⟨x, hDO hx⟩, hx⟩
  · intro t
    constructor
    · change ((J t).map ∘ (Subtype.val : O → D.extension.Point)) ''
        (Subtype.val ⁻¹' D.carrier) = _
      rw [image_comp, D.image_restrict_carrier O hDO]
      exact (himages t).1
    · rw [D.frontier_restrict_carrier O]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hm : (J t).map x.val ∈ (J t).map '' frontier D.carrier := ⟨x.val, hx, rfl⟩
        rwa [(himages t).2] at hm
      · intro hy
        have hm : y ∈ (J t).map '' frontier D.carrier := by rwa [(himages t).2]
        obtain ⟨x, hx, heq⟩ := hm
        exact ⟨⟨x, hDO (D.compact.isClosed.frontier_subset hx)⟩, hx, heq⟩
  · intro t k x hx
    rw [hprimitive]
    exact E.extension.pullback_rankTwoPrimitive_eq_of_tangent_range_le_kernel (lgManifold n)
      (K t) (lambdaPotentialForm φ) (tailoringFamily I β t.val) k x (le_of_eq (hKkernel t x hx))

end FsFltz
