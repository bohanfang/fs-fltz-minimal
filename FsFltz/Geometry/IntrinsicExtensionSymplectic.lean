import FsFltz.Geometry.IntrinsicPrimitiveExtension
import FsFltz.Geometry.IntrinsicExteriorNaturality

/-!
# Symplectic primitive extension on the literal intrinsic carrier

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 119–160, and `sec:lean`,
lines 783–814. Actual exterior naturality on every native tangent transports
source nondegeneracy through the produced inclusion's bijective differential.
The constructed compact carrier therefore carries the actual smooth closed
symplectic differential of the single glued primitive. No completed flow or
geometric comparison is asserted here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry.IntrinsicLiouville

variable {k : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]
  [IsManifold (𝓡∂ (k + 1)) ∞ M]

/-- If an actual smooth primitive pullback is nondegenerate, a bijective
actual differential transports nondegeneracy to the boundaryless ambient. -/
theorem nondegenerate_exteriorDerivative_of_native_pullback {d : ℕ}
    (N : SmoothManifold d) (f : M → N.Point)
    (hf : ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) ∞ f)
    (lam : N.Form 1) (hlam : N.IsSmoothForm lam) (α : Form k M 1)
    (hpull : (fun x => (lam (f x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x)) = α)
    (x : M) (hbij : Function.Bijective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x))
    (hnd : Nondegenerate (exteriorDerivative α) x) :
    N.Nondegenerate (N.exteriorDerivative lam) (f x) := by
  have hd := exteriorDerivative_pullback_from_boundaryless N f hf lam hlam
  rw [hpull] at hd
  let A := mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model d) f x
  intro v hv
  obtain ⟨u, hu⟩ := hbij.2 v
  have hu0 : u = 0 := by
    apply hnd
    intro w
    have heval := congrArg (fun omega => omega ![u, w]) (congrFun hd x)
    have ht : (fun j : Fin 2 => A (![u, w] j)) = ![A u, A w] := by
      funext j
      fin_cases j <;> rfl
    change exteriorDerivative α x ![u, w] =
      N.exteriorDerivative lam (f x) (fun j => A (![u, w] j)) at heval
    rw [ht, hu] at heval
    exact heval.trans (hv (A w))
  simpa only [hu0, map_zero] using hu.symm

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The original locally smooth primitive, nondegenerate derivative, and
outward local defining functions produce an actual compact-domain
presentation with a globally smooth primitive extending the entire source
primitive and symplectic differential on the literal carrier. No collar,
atlas, primitive matching law, or domain presentation is required as input. -/
theorem exists_compactDomain_with_symplectic_primitive_extension
    (α : Form k M 1) (hα : IsLocallyExtendibleForm α)
    (hnd : ∀ x, Nondegenerate (exteriorDerivative α) x)
    (hout : ∀ x : IntrinsicBoundary.Point k M,
      ∃ (rho : M → ℝ) (beta : Model (k + 1) → ℝ),
        rho x.val = 0 ∧
        (∀ᶠ y in 𝓝 x.val, rho y ≤ 0) ∧
        mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val ≠ 0 ∧
        ContDiffAt ℝ ∞ beta ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val) ∧
        beta =ᶠ[𝓝[((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).target]
          ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1)) x.val)]
          (rho ∘ ((IntrinsicBoundary.chartAt x).ambient.extend (𝓡∂ (k + 1))).symm) ∧
        0 < (show ℝ from mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, ℝ) rho x.val
          (liouvilleVector α (exteriorDerivative α) x.val))) :
    ∃ (D : CompactDomain (k + 1)) (i : M → D.extension.Point) (lam : D.extension.Form 1),
      ContMDiff (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) ∞ i ∧
      Topology.IsClosedEmbedding i ∧
      (∀ x, Function.Bijective (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) ∧
      range i = D.carrier ∧
      frontier D.carrier = i '' (𝓡∂ (k + 1)).boundary M ∧
      D.extension.IsSmoothForm lam ∧
      (fun x => (lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = α ∧
      (fun x => (D.extension.exteriorDerivative lam (i x)).compContinuousLinearMap
        (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x)) = exteriorDerivative α ∧
      D.extension.IsSymplecticOn (D.extension.exteriorDerivative lam) D.carrier := by
  obtain ⟨D, i, lam, hi, hemb, hbij, hrange, hfrontier, hlam, hpull⟩ :=
    exists_compactDomain_with_smooth_primitive_extension α hα hnd hout
  have hd := exteriorDerivative_pullback_from_boundaryless D.extension i hi lam hlam
  rw [hpull] at hd
  refine ⟨D, i, lam, hi, hemb, hbij, hrange, hfrontier, hlam, hpull, hd.symm, ?_⟩
  apply (D.extension.isSymplecticOn_exteriorDerivative_iff lam hlam D.carrier).mpr
  intro z hz
  rw [← hrange] at hz
  obtain ⟨x, rfl⟩ := hz
  exact nondegenerate_exteriorDerivative_of_native_pullback D.extension i hi lam hlam α
    hpull x (hbij x) (hnd x)

end FsFltz.Geometry.IntrinsicLiouville
