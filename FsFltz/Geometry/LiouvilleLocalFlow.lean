import FsFltz.Geometry.LiouvilleNeighborhood
import FsFltz.Geometry.CollarSmoothEvolution

/-!
# Constructed two-sided local Liouville flow

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–158, and `sec:lean`,
lines 783–814. The contraction equation is available on the actual open
symplectic neighborhood constructed in `LiouvilleNeighborhood`.

The mathematical route is to cut a smooth vector field off near a compact
set. Compactness provides a uniform local integration time on its support;
outside the support constant curves solve the equation. Native continuation
therefore gives all-real curves of the auxiliary field. Uniqueness gives
their action law, and the proved Picard dependence theorem gives joint
`C∞` regularity. The tube lemma then provides an open neighborhood of the
original compact set and a positive two-sided time interval on which every
trajectory stays where the cutoff equals one. On that interval it solves
the original field's equation.

The resulting action is globally defined for an auxiliary field, and is a
Liouville flow only on the specified local interval and neighborhood. This
does not claim completeness of the original field. No completion, collar,
flow, or GPS input is supplied. Boundary collar inversion, the exponential
primitive law, and completion gluing are separate downstream obligations.
-/

noncomputable section
open scoped Manifold ContDiff Classical
open Set Filter Topology Function

namespace FsFltz.Geometry
namespace CollarFlow

section Supported

variable {E H Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [CompleteSpace E] [FiniteDimensional ℝ E] [T2Space Q]

set_option backward.isDefEq.respectTransparency false in
/-- Native-model version of compactly supported integration, allowing the
product model of parameter times spatial manifold without changing charts. -/
theorem exists_supported_smoothFlow
    (Z : (x : Q) → TangentSpace I x)
    (hZ : ContMDiff I I.tangent ∞
      (fun x => (⟨x, Z x⟩ : TangentBundle I Q)))
    {K : Set Q} (hK : IsCompact K) (hzero : ∀ x ∉ K, Z x = 0) :
    ∃ F : Flow ℝ Q,
      ContMDiff ((𝓘(ℝ, ℝ)).prod I) I ∞
        (fun p : ℝ × Q => F p.1 p.2) ∧
      ∀ x, IsMIntegralCurve (fun t => F t x) Z := by
  have hv₁ := hZ.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  obtain ⟨ε, hε, H⟩ := exists_compact_uniform_local_integralCurve hv₁ hK
  have hlocal : ∀ x : Q, ∃ γ : ℝ → Q,
      γ 0 = x ∧ IsMIntegralCurveOn γ Z (Ioo (-ε) ε) := by
    intro x
    by_cases hx : x ∈ K
    · exact H x hx
    · refine ⟨fun _ => x, rfl, ?_⟩
      intro t _
      rw [hzero x hx]
      simpa only [ContinuousLinearMap.smulRight_zero] using
        (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := I) x t).hasMFDerivWithinAt
  have hglobal := exists_isMIntegralCurve_of_isMIntegralCurveOn hv₁ hε hlocal
  choose γ hγ₀ hγ using hglobal
  let φ : ℝ → Q → Q := fun t x => γ x t
  have hself : ∀ x, φ 0 x = x := hγ₀
  have hcomp : ∀ s t x, φ (s + t) x = φ s (φ t x) := by
    intro s t x
    exact (congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
      (t₀ := 0) hv₁ (hγ (φ t x)) ((hγ x).comp_add t)
      (by simp only [comp_apply, zero_add, hγ₀]; rfl)) s).symm
  have hs := contMDiff_joint_of_isMIntegralCurve hZ φ hself hγ
  exact ⟨⟨φ, hs.continuous, hcomp, hself⟩, hs, hγ⟩

end Supported

end CollarFlow
namespace SmoothManifold

set_option backward.isDefEq.respectTransparency false in
/-- A smooth autonomous field vanishing outside a compact set has a
constructed jointly smooth all-real flow solving its actual native ODE. -/
theorem exists_supported_smoothFlow {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorField Z)
    {K : Set M.Point} (hK : IsCompact K) (hzero : ∀ x ∉ K, Z x = 0) :
    ∃ F : Flow ℝ M.Point,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => F p.1 p.2) ∧
      ∀ x, IsMIntegralCurve (fun t => F t x) Z := by
  exact CollarFlow.exists_supported_smoothFlow Z hZ.contMDiff_section hK hzero

set_option backward.isDefEq.respectTransparency false in
/-- Construct an auxiliary smooth action which solves the given field's
ODE on one common two-sided time interval and an open neighborhood of the
entire compact set. Its global action law refers to the cutoff field. -/
theorem exists_local_smoothFlow {d : ℕ} (M : SmoothManifold d)
    (Z : (x : M.Point) → M.Tangent x) (hZ : M.IsSmoothVectorField Z)
    {K : Set M.Point} (hK : IsCompact K) :
    ∃ (U : TopologicalSpace.Opens M.Point) (δ : ℝ),
      K ⊆ (U : Set M.Point) ∧ 0 < δ ∧ ∃ F : Flow ℝ M.Point,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × M.Point => F p.1 p.2) ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => F s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (F t x))) := by
  obtain ⟨χ, V, hχ, hKV, hone, hsupport, _⟩ :=
    CollarExtension.exists_smooth_compact_cutoff (I := 𝓘(ℝ, Model d))
      hK isOpen_univ (subset_univ K)
  let W : (x : M.Point) → M.Tangent x := fun x => χ x • Z x
  have hW : M.IsSmoothVectorField W :=
    M.isSmoothVectorField_of_contMDiff_section (hχ.smul_section hZ.contMDiff_section)
  obtain ⟨F, hF, hode⟩ := M.exists_supported_smoothFlow W hW hsupport
    (fun x hx => by simp only [W, image_eq_zero_of_notMem_tsupport hx, zero_smul])
  let S : Set (ℝ × M.Point) := (fun p : ℝ × M.Point => F p.1 p.2) ⁻¹' V
  have hS : IsOpen S := V.isOpen.preimage hF.continuous
  have hseam : ({0} : Set ℝ) ×ˢ K ⊆ S := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    simp only [mem_singleton_iff] at ht
    subst t
    simpa only [S, mem_preimage, Flow.map_zero_apply] using hKV hx
  obtain ⟨T, A, hT, hA, hzeroT, hKA, hTA⟩ :=
    generalized_tube_lemma isCompact_singleton hK hS hseam
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hT.mem_nhds (hzeroT (mem_singleton 0)))
  refine ⟨⟨A, hA⟩, δ, hKA, hδ, F, hF, ?_⟩
  intro x hx t ht
  have htT : t ∈ T := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using ht)
  have hFV : F t x ∈ V := show (t, x) ∈ S from hTA ⟨htT, hx⟩
  simpa only [W, hone _ hFV, one_smul] using hode x t

end SmoothManifold

namespace LiouvilleDomain

set_option backward.isDefEq.respectTransparency false in
/-- The canonical Liouville field on the constructed symplectic open
extension has an actual joint `C∞` local flow on one neighborhood of the
compact domain and one uniform positive two-sided time interval. -/
theorem exists_neighborhood_localFlow {d : ℕ} (D : LiouvilleDomain d) :
    ∃ (U : TopologicalSpace.Opens D.neighborhoodDomain.extension.Point) (δ : ℝ),
      D.neighborhoodDomain.carrier ⊆ (U : Set D.neighborhoodDomain.extension.Point) ∧
      0 < δ ∧ ∃ F : Flow ℝ D.neighborhoodDomain.extension.Point,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Model d)) 𝓘(ℝ, Model d) ∞
        (fun p : ℝ × D.neighborhoodDomain.extension.Point => F p.1 p.2) ∧
      ∀ x ∈ U, ∀ t ∈ Ioo (-δ) δ,
        HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Model d) (fun s => F s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (D.neighborhoodStructure.field (F t x))) :=
  D.neighborhoodDomain.extension.exists_local_smoothFlow
    D.neighborhoodStructure.field D.neighborhoodStructure.smooth_field D.neighborhoodDomain.compact

end LiouvilleDomain
end FsFltz.Geometry
