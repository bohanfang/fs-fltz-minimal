import FsFltz.Geometry.TailoringRibbonOutward
import FsFltz.Geometry.IntrinsicNativeCompletionFamilyFields
import FsFltz.Geometry.SmoothFormOpenGluing
import FsFltz.Geometry.PairFamilyConstruction

/-!
# Liouville pullback on a transported compact carrier

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 991–1009.
An equal-dimensional smooth embedding pulls the actual symplectic primitive
back to a compact carrier. Its literal sublevel and boundary images transfer
outwardness to the carrier's stored native defining functions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry.CompactDomain
open SmoothManifold

/-- Construct the native Liouville structure from the actual embedded
sublevel geometry. No outwardness or source symplecticity is assumed. -/
theorem exists_liouvilleStructure_of_sublevel_pullback {d : ℕ}
    (D : CompactDomain d) (M : SmoothManifold d) (j : D.extension.SmoothEmbedding M)
    (α : M.Form 1) (hα : M.IsSmoothForm α)
    (hnd : ∀ y, M.Nondegenerate (M.exteriorDerivative α) y)
    (q : M.Point → ℝ) (hq : ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ q)
    (hside : ∀ x ∈ D.carrier, q (j.map x) ≤ 0)
    (hzero : ∀ x ∈ frontier D.carrier, q (j.map x) = 0)
    (hout : ∀ x ∈ frontier D.carrier,
      0 < M.scalarDerivative q (j.map x) (M.liouvilleVector α (j.map x))) :
    ∃ L : LiouvilleStructure D,
      L.primitive = D.extension.pullback M j.map α ∧
      L.field = D.extension.liouvilleVector (D.extension.pullback M j.map α) ∧
      D.extension.IsSymplecticOn (D.extension.exteriorDerivative L.primitive) univ ∧
      ∀ x, mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.map x (L.field x) =
        M.liouvilleVector α (j.map x) := by
  let μ := D.extension.pullback M j.map α
  have hμ : D.extension.IsSmoothForm μ := D.extension.isSmoothForm_pullback_one M j.map α hα
  have hμnd (x : D.extension.Point) : D.extension.Nondegenerate
      (D.extension.exteriorDerivative μ) x :=
    D.extension.nondegenerate_exteriorDerivative_pullback M j.map j.map.contMDiff α hα x
      ⟨j.immersion x, LinearMap.injective_iff_surjective.mp (j.immersion x)⟩ (hnd _)
  have hsym : D.extension.IsSymplecticOn (D.extension.exteriorDerivative μ) univ :=
    (D.extension.isSymplecticOn_exteriorDerivative_iff μ hμ univ).mpr (fun x _ => hμnd x)
  have hmap (x : D.extension.Point) :
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) j.map x (D.extension.liouvilleVector μ x) =
        M.liouvilleVector α (j.map x) :=
    D.extension.map_liouvilleVector_of_primitive_pullback M rfl j.map j.map.contMDiff
      μ α hα rfl x (hμnd x) (hnd _)
  have ho : ∀ x (hx : x ∈ frontier D.carrier),
      0 < D.extension.scalarDerivative (D.defining x hx).rho x (D.extension.liouvilleVector μ x) := by
    intro x hx
    apply D.outward_of_sublevel_derivative (q ∘ j.map) (hq.comp j.map.contMDiff) hside hzero x hx
    unfold scalarDerivative
    rw [mfderiv_comp_apply x (hq.mdifferentiableAt (by simp))
      (j.map.contMDiff.mdifferentiableAt (by simp)), hmap]
    exact hout x hx
  let L : LiouvilleStructure D :=
    { primitive := μ
      smooth_primitive := hμ
      symplectic := ⟨hsym.1, fun x _ => hsym.2.1 x (mem_univ _),
        fun x _ => hμnd x⟩
      field := D.extension.liouvilleVector μ
      smooth_field := D.extension.isSmoothVectorField_liouvilleVector μ hμ hμnd
      contraction := fun x _ => D.extension.liouvilleVector_contraction μ x
        (D.extension.liouvilleEquation_exists μ x (hμnd x))
      outward := ho }
  exact ⟨L, rfl, rfl, hsym, hmap⟩

/-- Jointly smooth embeddings and primitives construct the actual family
of pulled-back Liouville structures and its localized completions. -/
theorem exists_liouvilleFamily_of_sublevel_pullback {d : ℕ}
    (D : CompactDomain d) (M : SmoothManifold d)
    (j : Parameter → D.extension.SmoothEmbedding M)
    (hj : D.extension.IsSmoothIntervalMapFamily M (fun t => (j t).map))
    (α : Parameter → M.Form 1) (hα : M.IsSmoothIntervalFormFamily α)
    (hnd : ∀ t y, M.Nondegenerate (M.exteriorDerivative (α t)) y)
    (q : Parameter → M.Point → ℝ)
    (hq : ∀ t, ContMDiff 𝓘(ℝ, Model d) 𝓘(ℝ, ℝ) ∞ (q t))
    (hside : ∀ t x, x ∈ D.carrier → q t ((j t).map x) ≤ 0)
    (hzero : ∀ t x, x ∈ frontier D.carrier → q t ((j t).map x) = 0)
    (hout : ∀ t x, x ∈ frontier D.carrier →
      0 < M.scalarDerivative (q t) ((j t).map x) (M.liouvilleVector (α t) ((j t).map x))) :
    ∃ L : Parameter → LiouvilleStructure D,
      (∀ t, (L t).primitive = D.extension.pullback M (j t).map (α t)) ∧
      D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) ∧
      D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) ∧
      (∀ t, D.extension.IsSymplecticOn (D.extension.exteriorDerivative (L t).primitive) univ) ∧
      Nonempty (LocalizedCompletionFamily D L) ∧
      ∀ t x, mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) (j t).map x ((L t).field x) =
        M.liouvilleVector (α t) ((j t).map x) := by
  classical
  have hex (t : Parameter) := D.exists_liouvilleStructure_of_sublevel_pullback M (j t) (α t)
    (M.isSmoothForm_of_isSmoothIntervalFormFamily α hα t) (hnd t) (q t) (hq t)
    (hside t) (hzero t) (hout t)
  choose L hprimitive hfield hsym hmap using hex
  have hsmooth : D.extension.IsSmoothIntervalFormFamily (fun t => (L t).primitive) := by
    have h := D.extension.isSmoothIntervalFormFamily_pullback_one M
      (fun t => (j t).map) hj α hα
    simpa only [hprimitive] using h
  have hsmoothfield : D.extension.IsSmoothIntervalVectorFieldFamily (fun t => (L t).field) := by
    have h := D.extension.isSmoothIntervalVectorFieldFamily_liouvilleVector
      (fun t => (L t).primitive) hsmooth (fun t x => (hsym t).2.2 x (mem_univ _))
    simpa only [hprimitive, hfield] using h
  exact ⟨L, hprimitive, hsmooth, hsmoothfield, hsym,
    D.exists_smooth_localizedCompletionFamily_of_liouvilleFamily L hsmooth, hmap⟩

end FsFltz.Geometry.CompactDomain
