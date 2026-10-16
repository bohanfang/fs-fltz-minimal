import FsFltz.Geometry.IntrinsicCompletionInclusion
import FsFltz.Geometry.CompactPrimitiveNaturality

/-!
# Native primitive inclusions into a prescribed raw ambient

Source: `geoemtric-part-fsf.tex`, `def:pair`, lines 141–158, and
`sec:lean`, lines 805–814. The smooth ambient and its primitive are
specified independently. Full native primitive pullback and a
same-dimensional immersion force the actual exterior derivative and
canonical Liouville field on the entire native image, including the seam.
The constructed local embedding retains that image and transports the
compact-domain field on its whole carrier.

No target field, symplecticity away from the native image, complete flow,
end equation, coverage, or completion is assumed or constructed here.
Realization of a prescribed global intrinsic completion remains pending.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology
open Set Filter

namespace FsFltz.Geometry
open SmoothManifold

namespace LiouvilleDomain

/-- Full primitive equality only on a compact carrier forces exterior
derivative equality, target nondegeneracy and actual Liouville-field
transport there. The target is a raw smooth manifold with a smooth primitive;
neither a target field nor target symplecticity is an input. -/
theorem inclusionEquations_of_primitive_on_carrier {d : ℕ}
    (D : LiouvilleDomain d) (N : SmoothManifold d)
    (lam : N.Form 1) (hlam : N.IsSmoothForm lam)
    (J : D.domain.extension.SmoothEmbedding N)
    (hp : ∀ z ∈ D.domain.carrier,
      D.domain.extension.pullback N J.map lam z = D.liouville.primitive z) :
    (∀ z ∈ D.domain.carrier,
      D.domain.extension.pullback N J.map (N.exteriorDerivative lam) z =
        D.domain.extension.exteriorDerivative D.liouville.primitive z) ∧
    (∀ z ∈ D.domain.carrier,
      N.Nondegenerate (N.exteriorDerivative lam) (J.map z)) ∧
    ∀ z ∈ D.domain.carrier,
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z (D.liouville.field z) =
        N.liouvilleVector lam (J.map z) := by
  have hdp := D.domain.exteriorDerivative_eqOn_of_eqOn
    (D.domain.extension.pullback N J.map lam) D.liouville.primitive
    (D.domain.extension.isSmoothForm_pullback_one N J.map lam hlam)
    D.liouville.smooth_primitive hp
  have hn := D.domain.extension.exteriorDerivative_pullback N J.map lam hlam
  have hd : ∀ z ∈ D.domain.carrier,
      D.domain.extension.pullback N J.map (N.exteriorDerivative lam) z =
        D.domain.extension.exteriorDerivative D.liouville.primitive z := by
    intro z hz
    exact (congrFun hn z).symm.trans (hdp z hz)
  have hbij (z : D.domain.extension.Point) : Function.Bijective
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z) :=
    ⟨J.immersion z, LinearMap.injective_iff_surjective.mp (J.immersion z)⟩
  have hnd : ∀ z ∈ D.domain.carrier,
      N.Nondegenerate (N.exteriorDerivative lam) (J.map z) := by
    intro z hz v hv
    obtain ⟨u, hu⟩ := (hbij z).2 v
    have hu0 : u = 0 := by
      apply D.liouville.symplectic.2.2 z hz
      intro w
      have he := congrArg (fun eta => eta ![u, w]) (hd z hz)
      have ht : (fun j : Fin 2 =>
          mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z (![u, w] j)) =
            ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z u,
              mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z w] := by
        funext j
        fin_cases j <;> rfl
      change N.exteriorDerivative lam (J.map z)
          (fun j => mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z (![u, w] j)) =
        D.domain.extension.exteriorDerivative D.liouville.primitive z ![u, w] at he
      rw [ht, hu] at he
      exact he.symm.trans (hv _)
    simpa only [hu0, map_zero] using hu.symm
  refine ⟨hd, hnd, ?_⟩
  intro z hz
  apply (N.liouvilleVector_eq lam (J.map z) (hnd z hz) ?_).symm
  intro w
  obtain ⟨v, rfl⟩ := (hbij z).2 w
  have he := congrArg (fun eta => eta ![D.liouville.field z, v]) (hd z hz)
  have ht : (fun j : Fin 2 =>
      mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z (![D.liouville.field z, v] j)) =
        ![mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z (D.liouville.field z),
          mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z v] := by
    funext j
    fin_cases j <;> rfl
  have hep := congrArg (fun eta => eta (fun _ => v)) (hp z hz)
  change evalOne lam (J.map z)
      (mfderiv 𝓘(ℝ, Model d) 𝓘(ℝ, Model d) J.map z v) =
        evalOne D.liouville.primitive z v at hep
  simp only [pullback, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def, ht] at he
  exact he.trans ((D.liouville.contraction z hz v).trans hep.symm)

end LiouvilleDomain

namespace IntrinsicLiouville.NativeLiouvillePresentation

variable {k : ℕ} {M : Type} [TopologicalSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (k + 1)) M]

/-- Original native inclusion germs construct an embedding near the whole
source carrier into the prescribed raw smooth ambient. Full primitive
preservation then derives the full exterior derivative and Liouville-field
laws on that same localized carrier. The given native inclusion, target
manifold and target primitive are retained exactly. -/
theorem exists_inclusionEmbedding_with_field_into_specified_manifold
    {α : Form k M 1} (P : NativeLiouvillePresentation α)
    (N : SmoothManifold (k + 1)) (lam : N.Form 1) (hlam : N.IsSmoothForm lam)
    (i : M → N.Point)
    (hi : IsLocallyExtendibleTargetMap (k := k) N i)
    (hinj : Function.Injective i)
    (himm : ∀ x, Function.Injective
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x))
    (hpull : ∀ x, (lam (i x)).compContinuousLinearMap
      (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) = α x) :
    ∃ (U : TopologicalSpace.Opens P.domain.domain.extension.Point)
      (hU : P.domain.domain.carrier ⊆ U)
      (J : (P.domain.domain.extension.restrict U).SmoothEmbedding N),
      (∀ x, J.map ((P.restrict U hU).inclusion x) = i x) ∧
      (∀ x,
        (mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) J.map
          ((P.restrict U hU).inclusion x)).comp
            (mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1))
              (P.restrict U hU).inclusion x) =
          mfderiv (𝓡∂ (k + 1)) 𝓘(ℝ, Model (k + 1)) i x) ∧
      (∀ z ∈ (P.domain.restrict U hU).domain.carrier,
        (P.domain.domain.extension.restrict U).pullback N J.map lam z =
          (P.domain.restrict U hU).liouville.primitive z) ∧
      (∀ z ∈ (P.domain.restrict U hU).domain.carrier,
        (P.domain.domain.extension.restrict U).pullback N J.map
            (N.exteriorDerivative lam) z =
          (P.domain.domain.extension.restrict U).exteriorDerivative
            (P.domain.restrict U hU).liouville.primitive z) ∧
      (∀ z ∈ (P.domain.restrict U hU).domain.carrier,
        N.Nondegenerate (N.exteriorDerivative lam) (J.map z)) ∧
      ∀ z ∈ (P.domain.restrict U hU).domain.carrier,
        mfderiv 𝓘(ℝ, Model (k + 1)) 𝓘(ℝ, Model (k + 1)) J.map z
            ((P.domain.restrict U hU).liouville.field z) =
          N.liouvilleVector lam (J.map z) := by
  obtain ⟨U, hU, J, hsquare, hdsquare, hp⟩ :=
    P.exists_inclusionEmbedding_into_specified_manifold N lam i hi hinj himm hpull
  obtain ⟨hd, hnd, hfield⟩ :=
    (P.domain.restrict U hU).inclusionEquations_of_primitive_on_carrier N lam hlam J hp
  exact ⟨U, hU, J, hsquare, hdsquare, hp, hd, hnd, hfield⟩

end IntrinsicLiouville.NativeLiouvillePresentation
end FsFltz.Geometry
