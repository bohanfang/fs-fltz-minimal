import FsFltz.Geometry.TailoringHittingWitnessRetained
import FsFltz.Geometry.TailoringHittingPrimitiveRetained
import FsFltz.Geometry.PairGermFamilyConstruction

/-!
# Exact weighted primitive on the retained hitting ribbon

Source: `geometric-part-fsf-proof.tex`, `eq:hittingprimitive`, lines 1851–1853,
and `eq:ribbonprimitive`, lines 1867–1869. The same intrinsic shrink, native
hitting map and positive boundary witness satisfy the compact primitive law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology

namespace FsFltz.Geometry.SmoothManifold

/-- Scalar multiplication of forms commutes with the actual tangent pullback. -/
theorem pullback_scalar_mul {d e r : ℕ} (M : SmoothManifold d) (N : SmoothManifold e)
    (j : M.Point → N.Point) (b : N.Point → ℝ) (α : N.Form r) (x : M.Point) :
    M.pullback N j (fun y => b y • α y) x = b (j x) • M.pullback N j α x := by
  ext v
  rfl

end FsFltz.Geometry.SmoothManifold

namespace FsFltz
open Geometry Geometry.SmoothManifold
local instance witnessPrimitiveCharts {n : ℕ} :
    ChartedSpace (Model (2 * n)) (LGSpace n) := (lgManifold n).charts
local instance witnessPrimitiveSmooth {n : ℕ} :
    IsManifold 𝓘(ℝ, Model (2 * n)) ∞ (LGSpace n) := (lgManifold n).smooth

namespace IntrinsicShrinkingData
variable {n : ℕ} {P : WitnessedPair n} (S : IntrinsicShrinkingData P)
    {R : P.ribbonDomain.domain.extension.SmoothEmbedding (lgManifold n)}
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (Q : FullFiberRibbonMarking P R f value φ)
    (U : TopologicalSpace.Opens Q.manifold.Point)
    (hU : ∀ x : S.extension, (S.fiberEmbedding Q parameterOne).map x ∈ U)

/-- The full-fiber primitive law passes through the same negative intrinsic
flow to the whole compact shrinking endpoint. -/
theorem hittingEmbedding_primitive
    (V : TopologicalSpace.Opens ℝ)
    (e : V → (Q.manifold.restrict U).SmoothEmbedding (lgManifold n)) (k : V)
    (H : Q.manifold.Point → LGSpace n) (T : Q.manifold.Point → ℝ)
    (he : ∀ x : U, (e k).map x = H x.val)
    (hH : ∀ x ∈ (U : Set Q.manifold.Point),
      MDifferentiableAt 𝓘(ℝ, Model (2 * n - 2)) 𝓘(ℝ, Model (2 * n)) H x)
    (α : (lgManifold n).Form 1)
    (hpull : ∀ x ∈ (U : Set Q.manifold.Point),
      Q.manifold.pullback (lgManifold n) H α x = Real.exp (T x) •
        Q.primitive.toCompleteLiouvilleManifold.primitive x)
    (x : S.extension) (hx : x ∈ (S.pair parameterOne).ribbonDomain.domain.carrier) :
    (S.pair parameterOne).ribbonDomain.domain.extension.pullback (lgManifold n)
      (S.hittingEmbedding Q U hU V e k).map α x =
        Real.exp (T ((S.fiberEmbedding Q parameterOne).map x)) •
          (S.pair parameterOne).ribbonDomain.liouville.primitive x := by
  let F := (S.pair parameterOne).ribbonDomain.domain.extension
  let q := S.fiberEmbeddingInto Q U hU
  have heq : ((e k).map : U → LGSpace n) = fun x : U => H x.val := funext he
  have hp (y : U) : (Q.manifold.restrict U).pullback (lgManifold n) (e k).map α y =
      Real.exp (T y.val) • (Q.manifold.restrict U).pullback Q.manifold Subtype.val
        Q.primitive.toCompleteLiouvilleManifold.primitive y := by
    rw [heq, Q.manifold.pullback_comp_restrict_val_of_mdifferentiableAt
      (lgManifold n) U H α y (hH y.val y.property), hpull y.val y.property]
    unfold SmoothManifold.pullback
    rw [Q.manifold.mfderiv_restrict_val]
    rfl
  change F.pullback (lgManifold n) ((e k).map ∘ q.map) α x = _
  rw [F.pullback_comp (Q.manifold.restrict U) (lgManifold n)
    (q.map.contMDiff.mdifferentiable (by simp))
    ((e k).map.contMDiff.mdifferentiable (by simp))]
  have hform := funext hp
  rw [hform, F.pullback_scalar_mul]
  have hq : (Subtype.val : U → Q.manifold.Point) ∘ q.map =
      (S.fiberEmbedding Q parameterOne).map := rfl
  rw [← F.pullback_comp (Q.manifold.restrict U) Q.manifold
    (q.map.contMDiff.mdifferentiable (by simp))
    ((contMDiff_subtype_val (I := 𝓘(ℝ, Model (2 * n - 2))) (n := ∞)).mdifferentiable (by simp)),
    hq, S.fiberEmbedding_primitive Q parameterOne x hx]
  rfl

end IntrinsicShrinkingData

/-- An exponential hitting primitive and its inverse-exponential boundary
witness give the exact weighted compact ribbon primitive. -/
theorem weighted_hitting_ribbon_primitive {d a b : ℕ}
    (F : SmoothManifold d) (B : SmoothManifold b) (M : SmoothManifold a)
    (j : F.SmoothEmbedding B) (i : B.SmoothEmbedding M)
    (e : F.Point → M.Point) (he : ∀ x, i.map (j.map x) = e x)
    (α : M.Form 1) (μ : F.Form 1) (T : F.Point → ℝ) (w : B.Point → ℝ)
    (x : F.Point)
    (hpull : F.pullback M e α x = Real.exp (T x) • μ x)
    (hw : w (j.map x) = Real.exp (-T x)) :
    F.pullback B j.map (fun y => w y • B.pullback M i.map α y) x = μ x := by
  rw [F.pullback_scalar_mul, hw,
    ← F.pullback_comp B M (j.map.contMDiff.mdifferentiable (by simp))
      (i.map.contMDiff.mdifferentiable (by simp))]
  have hmap : i.map ∘ j.map = e := funext he
  rw [hmap, hpull, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

end FsFltz
