import FsFltz.Geometry.Smooth

/-!
# Immersion of a parameter graph

The parameter graph `(t,x) ↦ (t,j(t,x))` has injective derivative exactly
when the spatial slice does. This supplies the derivative bridge used to
localize compact ribbon families; it applies also to dimension-zero ribbons.
Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 132–141,
`def:chain`, lines 163–169, and `sec:lean`, lines 783–814.
-/

noncomputable section
open scoped Manifold ContDiff
open Set Filter

namespace FsFltz.Geometry.SmoothManifold

set_option backward.isDefEq.respectTransparency false

/-- The graph derivative is triangular: its first component is the parameter
velocity, and its spatial component at zero parameter velocity is exactly the
derivative of the corresponding slice. No positive dimension is required. -/
theorem injective_mfderiv_parameterGraph_iff {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    {j : ℝ → M.Point → N.Point} {p : ℝ × M.Point}
    (hjs : MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
      (𝓘(ℝ, Model e)) (fun q => j q.1 q.2) p) :
    Function.Injective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
      ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model e))) (fun q => (q.1, j q.1 q.2)) p) ↔
    Function.Injective (mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) (j p.1) p.2) := by
  have hgraph (v : TangentSpace ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d))) p) :
      mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
        ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model e)))
        (fun q => (q.1, j q.1 q.2)) p v =
      (v.1, mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, Model e)) (fun t => j t p.2) p.1 v.1 +
        mfderiv (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) (j p.1) p.2 v.2) := by
    erw [mfderiv_prodMk mdifferentiableAt_fst hjs, mfderiv_fst]
    change (v.1, mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
      (𝓘(ℝ, Model e)) (fun q => j q.1 q.2) p v) = _
    rw [mfderiv_prod_eq_add_apply hjs]
  constructor
  · intro h v w hvw
    have he :
        mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
          ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model e)))
          (fun q => (q.1, j q.1 q.2)) p (0, v) =
        mfderiv ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
          ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model e)))
          (fun q => (q.1, j q.1 q.2)) p (0, w) := by
      rw [hgraph, hgraph]
      exact congrArg (fun z => (0, _ + z)) hvw
    exact congrArg Prod.snd (h he)
  · intro h v w hvw
    rw [hgraph, hgraph] at hvw
    have ht : v.1 = w.1 := congrArg (fun z : ℝ × Model e => z.1) hvw
    have hs := congrArg (fun z : ℝ × Model e => z.2) hvw
    dsimp only at hs
    rw [ht] at hs
    exact Prod.ext ht (h (add_left_cancel hs))

/-- Joint smoothness on a genuine open parameter domain gives smoothness of
the spatial slice at each point of that domain. -/
theorem contMDiffAt_slice_of_joint {d e : ℕ}
    (M : SmoothManifold d) (N : SmoothManifold e)
    {j : ℝ → M.Point → N.Point} {W : Set (ℝ × M.Point)} {p : ℝ × M.Point}
    (hW : IsOpen W)
    (hjs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, Model d)))
      (𝓘(ℝ, Model e)) ∞ (fun q => j q.1 q.2) W) (hp : p ∈ W) :
    ContMDiffAt (𝓘(ℝ, Model d)) (𝓘(ℝ, Model e)) ∞ (j p.1) p.2 := by
  exact (hjs.contMDiffAt (hW.mem_nhds hp)).comp
    (f := fun x : M.Point => (p.1, x)) p.2
    (contMDiffAt_const.prodMk contMDiffAt_id)

end FsFltz.Geometry.SmoothManifold
