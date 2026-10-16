import FsFltz.Geometry.IntrinsicShrinkingPairNeighborhood
import FsFltz.Geometry.TailoringMarkedPrefixCore

/-!
# Intrinsic shrinking of the actual finite-input marked prefix

Source: `geometric-part-fsf-proof.tex`, `subsec:junction`, lines 1876–1905.
The full-fiber marking and full core are produced for the very same retained
prefix. Shrinking consumes those produced data without a separate choice of
potential, compact ribbon, or comparison chain.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Topology Classical
open Set Filter Topology

namespace FsFltz
open Geometry Geometry.SmoothManifold

/-- A full-fiber marking provides the actual continuous completed-fiber map
needed to shrink the entire retained compact ribbon into a core neighborhood. -/
theorem FullFiberRibbonMarking.exists_shrinking_into {n : ℕ} {P : WitnessedPair n}
    (A : P.ambientDomain.domain.boundary.SmoothEmbedding (lgManifold n))
    {f : LGSpace n → ℂ} {value : ℂ} {φ : RealSpace n → ℝ}
    (M : FullFiberRibbonMarking P (A.comp P.ribbonEmbedding) f value φ)
    (hP : P.ribbonDomain.domain.carrier.Nonempty)
    (W : TopologicalSpace.Opens (LGSpace n))
    (hcore : (A.comp P.ribbonEmbedding).map '' P.ribbonCompletion.core ⊆ (W : Set (LGSpace n))) :
    ∃ (Q : WitnessedPair n)
      (B : Q.ambientDomain.domain.boundary.SmoothEmbedding (lgManifold n))
      (chain : ComparisonChain P Q),
      Q.ambientDomain = P.ambientDomain ∧
      Q.ambientCompletion.ambient = P.ambientCompletion.ambient ∧
      (∀ datum : P.Maslov, ∃ target : Q.Maslov,
        Nonempty (GradedComparisonChain P chain datum target)) ∧
      ((B.comp Q.ribbonEmbedding).map '' Q.ribbonDomain.domain.carrier ⊆ (W : Set (LGSpace n))) ∧
      (B.comp Q.ribbonEmbedding).map '' Q.ribbonCompletion.core =
        (A.comp P.ribbonEmbedding).map '' P.ribbonCompletion.core := by
  apply P.exists_shrinking_into hP (lgManifold n) A
    (M.embedding.map ∘ M.marking.equiv)
    (M.embedding.map.contMDiff.continuous.comp M.marking.equiv.contMDiff.continuous)
    _ W hcore
  intro x hx
  change M.embedding.map (M.marking.equiv (P.ribbonCompletion.inclusion.map x)) = _
  rw [M.marking.inclusion (⟨x, hx⟩ : P.ribbonDomain.domain.Point)]
  exact M.compact_square ⟨x, hx⟩

/-- Finite toric input supplies the same-potential, literal full-core marked
prefix and a graded permitted shrinking comparison from its actual P7 pair
into every prescribed open neighborhood of that full core. -/
theorem ToricInput.exists_uniform_original_marked_prefix_shrinking {n : ℕ}
    (I : ToricInput n) :
    ∃ φEnd φ : RealSpace n → ℝ,
      IsStronglyCompatibleEndPotential I φEnd ∧ ContDiff ℝ 1 φEnd ∧ ContDiff ℝ ∞ φ ∧
      ∃ c U : ℝ, 0 < c ∧ 0 < U ∧
      (∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v) ∧
      (∀ u v : EuclideanSpace ℝ (Fin n),
        inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v ≤ U * ‖v‖ ^ 2) ∧
      (∃ L > 0, ∀ u, L ≤ ‖(EuclideanSpace.equiv (Fin n) ℝ).symm u‖ → φ u = φEnd u) ∧
      ∃ Aamb Cminus Cplus β₀ : ℝ, AmbientEndBound I Aamb ∧
        0 < Cminus ∧ Cminus < Cplus ∧ 0 < β₀ ∧ ∀ β ≥ β₀,
        max 1 (sublevelMagnitudeSup I Aamb) < Real.exp β ∧
        RatioSetWellDefined I (Real.exp β) ∧
        (∃ Afib : ℝ, FiberEndBound I Aamb (Real.exp β) Afib ∧
          Afib < Cminus ^ 2 * β ^ 2 / 2) ∧
        ∀ originalK : ℝ, K0 I (Real.exp β) ≤ originalK →
          ∃ K : ℝ, 0 < K ∧ originalK ≤ K / Real.exp β ^ 2 ∧
          ∃ m : RoundingChoice,
            GeometricAdmissibleRounding I (Real.exp β) originalK
              (Cminus ^ 2 * β ^ 2 / 2) (Cplus ^ 2 * β ^ 2 / 2) m ∧
            ∃ P : PotentialTailoringOriginalMarkedPrefix I φ β Cplus
              (Cminus ^ 2 * β ^ 2 / 2) originalK K m,
              ((P.marked.tailoring.embedding parameterOne).comp
                (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
                  P.marked.tailoring.deformation.target.ribbonEmbedding)).map ''
                P.marked.tailoring.deformation.target.ribbonCompletion.core =
                  tailoringCoreSection I φEnd β ∧
              ∀ W : TopologicalSpace.Opens (LGSpace n), tailoringCoreSection I φEnd β ⊆ (W : Set (LGSpace n)) →
                ∃ (Q : WitnessedPair n)
                  (B : Q.ambientDomain.domain.boundary.SmoothEmbedding (lgManifold n))
                  (chain : ComparisonChain P.marked.tailoring.deformation.target Q),
                  Q.ambientDomain = P.marked.tailoring.deformation.target.ambientDomain ∧
                  Q.ambientCompletion.ambient =
                    P.marked.tailoring.deformation.target.ambientCompletion.ambient ∧
                  (∀ datum : P.marked.tailoring.deformation.target.Maslov,
                    ∃ target : Q.Maslov, Nonempty
                      (GradedComparisonChain P.marked.tailoring.deformation.target chain datum target)) ∧
                  ((B.comp Q.ribbonEmbedding).map '' Q.ribbonDomain.domain.carrier ⊆ (W : Set (LGSpace n))) ∧
                  (B.comp Q.ribbonEmbedding).map '' Q.ribbonCompletion.core =
                    tailoringCoreSection I φEnd β := by
  obtain ⟨φEnd, φ, hstrong, hEnd, hφ, c, U, hc, hU, hlower, hupper, hend,
    Aamb, Cminus, Cplus, β₀, hamb, hminus, hplus, hβ₀, hparams⟩ :=
    I.exists_uniform_original_marked_prefix_fullCore
  refine ⟨φEnd, φ, hstrong, hEnd, hφ, c, U, hc, hU, hlower, hupper, hend,
    Aamb, Cminus, Cplus, β₀, hamb, hminus, hplus, hβ₀, ?_⟩
  intro β hβ
  obtain ⟨hR, hratio, hfib, hprefix⟩ := hparams β hβ
  refine ⟨hR, hratio, hfib, ?_⟩
  intro originalK hK
  obtain ⟨K, hKpos, hKL, m, hm, P, hcore⟩ := hprefix originalK hK
  refine ⟨K, hKpos, hKL, m, hm, P, hcore, ?_⟩
  intro W hW
  let A := (P.marked.tailoring.embedding parameterOne).comp
    P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion
  have hA : (A.comp P.marked.tailoring.deformation.target.ribbonEmbedding).map =
    ((P.marked.tailoring.embedding parameterOne).comp
      (P.marked.tailoring.deformation.target.ambientDomain.domain.boundaryInclusion.comp
        P.marked.tailoring.deformation.target.ribbonEmbedding)).map := rfl
  obtain ⟨Q, B, chain, hambient, hcompleted, hgrade, hsub, hQcore⟩ :=
    (P.marked.tailoring.ribbon_marking parameterOne).exists_shrinking_into A
      (P.marked.tailoring.ribbon_nonempty parameterOne) W (by rw [hA, hcore]; exact hW)
  refine ⟨Q, B, chain, hambient, hcompleted, hgrade, hsub, ?_⟩
  exact hQcore.trans (by rw [hA]; exact hcore)

end FsFltz
