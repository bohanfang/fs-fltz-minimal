import FsFltz.Geometry.TailoringRibbonNonempty

/-!
# Compact actual tailoring ribbon total spaces

Source: `geometric-part-fsf-proof.tex`, `lem:markedfamily`, lines 975–1009,
and `sec:assembly`, lines 2159–2166. The literal total space is a closed
subset of the product of the compact parameter interval and the proved
compact ambient potential sublevel. Its actual parameter projection is
proper and hits every parameter once the uniform truncation threshold is
met. A bundle atlas or completed-family correspondence is not assumed.
-/

noncomputable section
open scoped Manifold ContDiff Topology
open Set

namespace FsFltz.Geometry

variable {n : ℕ}

section Compactness

variable {φ φEnd : RealSpace n → ℝ} {c : ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hEnd1 : ContDiff ℝ 1 φEnd)
    (hEnd : ∀ u ≠ 0, ContDiffAt ℝ ∞ φEnd u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u, φEnd (r • u) = r ^ 2 * φEnd u)
    (hc : 0 < c)
    (hlower : ∀ u v : EuclideanSpace ℝ (Fin n), c * ‖v‖ ^ 2 ≤
      inner ℝ (fderiv ℝ (gradient (φ ∘ EuclideanSpace.equiv (Fin n) ℝ)) u v) v)
    {L : ℝ} (hL : 0 < L)
    (hend : ∀ u, L ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ → φ u = φEnd u)

include hφ hEnd1 hEnd hhom hc hlower hL hend

/-- The literal closed tailoring-ribbon total space is compact, at every
parameter scale and potential level, including possibly empty sublevels. -/
theorem isCompact_tailoringFamily_truncatedTotalSpace (I : ToricInput n) (β A : ℝ) :
    IsCompact {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} := by
  have hbase := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).prod
    (isCompact_potential_sublevel hφ hEnd1 hEnd hhom hc hlower hL hend A)
  have hclosed : IsClosed {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} := by
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_eq (contMDiff_tailoringFamily I β).continuous continuous_const).inter
        (isClosed_le (hφ.continuous.comp (continuous_fst.comp continuous_snd))
          continuous_const))
  exact hbase.of_isClosed_subset hclosed (fun _ hp => ⟨hp.1, hp.2.2⟩)

/-- The actual projection of the literal total space is a proper map;
this uses its compactness and the Hausdorff real parameter line. -/
theorem isProperMap_tailoringFamily_truncatedTotalSpace_proj (I : ToricInput n) (β A : ℝ) :
    IsProperMap (fun p : {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} => p.val.1) := by
  let : CompactSpace {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
      tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} :=
    isCompact_iff_compactSpace.mp
      (isCompact_tailoringFamily_truncatedTotalSpace hφ hEnd1 hEnd hhom hc hlower hL hend I β A)
  exact (continuous_fst.comp continuous_subtype_val).isProperMap

end Compactness

/-- The actual compact ribbon total spaces project onto the whole stated
closed interval, uniformly in every sufficiently large tailoring scale and
potential level. No nonemptiness or parameter trivialization is supplied
as an input. -/
theorem _root_.FsFltz.tailoringFamily_exists_uniform_truncatedTotalSpace_projection
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
        Prod.fst '' {p : ℝ × LGSpace n | p.1 ∈ Icc (0 : ℝ) 1 ∧
          tailoringFamily I β p.1 p.2 = 1 ∧ φ p.2.1 ≤ A} = Icc (0 : ℝ) 1 := by
  obtain ⟨F, hF, β₀, hβ₀, hne⟩ := tailoringFamily_exists_uniform_nonempty_fiber_truncations
    I hφ hc hU hlower hupper hEnd1 hEnd hhom hL hend
  refine ⟨F, hF, β₀, hβ₀, ?_⟩
  intro β hβ A hA
  apply subset_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  · intro s hs
    obtain ⟨y, hy⟩ := hne β hβ s hs A hA
    exact ⟨(s, y), ⟨hs, hy⟩, rfl⟩

end FsFltz.Geometry
