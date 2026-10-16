import FsFltz.Analysis.SupportMollification

/-!
# Compact polar facets of the actual toric input

Source: `geometric-part-fsf-proof.tex`, polar notation, lines 522–526,
`eq:strong`, lines 557–565, and `lem:potential`, lines 617–624.
These are the literal support-height unit sublevel and its generator
level faces. Compactness and exclusion of zero support the single small
quadratic perturbation preserving all facet open-star inclusions.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators Topology

variable {n : ℕ}

/-- The actual polar polytope, specified by all input vertex inequalities. -/
def polarPolytope (I : ToricInput n) : Set (RealSpace n) :=
  {x | supportHeight I x ≤ 1}

/-- The polar face on which the prescribed generator pairing is one. -/
def polarFacet (I : ToricInput n) (v : Lattice n) : Set (RealSpace n) :=
  {x | x ∈ polarPolytope I ∧ pairing v x = 1}

/-- The support-height definition is exactly the intersection of the
original polar half-space inequalities. -/
theorem mem_polarPolytope_iff (I : ToricInput n) (x : RealSpace n) :
    x ∈ polarPolytope I ↔ ∀ v ∈ I.vertices, pairing v x ≤ 1 := by
  constructor
  · intro hx v hv
    exact (I.pairing_le_supportHeight x ⟨v, hv⟩).trans hx
  · intro hx
    obtain ⟨v, hv⟩ := I.supportHeight_attained x
    change supportHeight I x ≤ 1
    rw [← hv]
    exact hx v.val v.property

theorem isClosed_polarPolytope (I : ToricInput n) : IsClosed (polarPolytope I) :=
  isClosed_le I.supportHeight_continuous continuous_const

/-- Interior zero and the proved support-height lower bound make the
actual polar compact, with no boundedness assumption on the input. -/
theorem isCompact_polarPolytope (I : ToricInput n) : IsCompact (polarPolytope I) := by
  obtain ⟨c, hc, _, _, hbounds⟩ := I.exists_supportHeight_linear_bounds
  apply (isCompact_closedBall (0 : RealSpace n) (1 / c)).of_isClosed_subset
    (isClosed_polarPolytope I)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖x‖ ≤ Real.sqrt (realSquaredNorm x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    simpa [EuclideanSpace.norm_eq, realSquaredNorm, Real.norm_eq_abs]
      using PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) j
  apply (le_div_iff₀ hc).mpr
  have hlow := (hbounds x).1
  have hcompare := mul_le_mul_of_nonneg_left hnorm hc.le
  change supportHeight I x ≤ 1 at hx
  nlinarith

theorem isClosed_polarFacet (I : ToricInput n) (v : Lattice n) :
    IsClosed (polarFacet I v) := by
  exact (isClosed_polarPolytope I).inter
    (isClosed_eq (by unfold pairing; fun_prop) continuous_const)

/-- Each actual polar facet is compact, the hypothesis needed for one
uniformly small quadratic gradient perturbation. -/
theorem isCompact_polarFacet (I : ToricInput n) (v : Lattice n) :
    IsCompact (polarFacet I v) := by
  exact (isCompact_polarPolytope I).inter_right
    (isClosed_eq (by unfold pairing; fun_prop) continuous_const)

/-- No polar facet contains the origin, even for a proposed generator
which is not an input vertex. -/
theorem ne_zero_of_mem_polarFacet (I : ToricInput n) (v : Lattice n)
    {x : RealSpace n} (hx : x ∈ polarFacet I v) : x ≠ 0 := by
  intro he
  have hpair := hx.2
  simp [he, pairing] at hpair

/-- On an actual vertex facet the support height is exactly one. -/
theorem supportHeight_eq_one_of_mem_polarFacet (I : ToricInput n)
    {v : Lattice n} (hv : v ∈ I.vertices) {x : RealSpace n}
    (hx : x ∈ polarFacet I v) : supportHeight I x = 1 := by
  apply le_antisymm hx.1
  rw [← hx.2]
  exact I.pairing_le_supportHeight x ⟨v, hv⟩

/-- The facet generator is a maximizer, as needed by the positive
convolution-coefficient producer. -/
theorem pairing_eq_supportHeight_of_mem_polarFacet (I : ToricInput n)
    {v : Lattice n} (hv : v ∈ I.vertices) {x : RealSpace n}
    (hx : x ∈ polarFacet I v) : pairing v x = supportHeight I x := by
  rw [supportHeight_eq_one_of_mem_polarFacet I hv hx]
  exact hx.2

/-- The actual polar boundary is contained in the support-height one
level, by continuity of the defining support function. -/
theorem supportHeight_eq_one_of_mem_frontier_polarPolytope (I : ToricInput n)
    {x : RealSpace n} (hx : x ∈ frontier (polarPolytope I)) :
    supportHeight I x = 1 := by
  exact frontier_le_subset_eq I.supportHeight_continuous continuous_const hx

/-- Each support-height one point belongs to a literal facet for an
actual input vertex, furnished by finite maximum attainment. -/
theorem exists_mem_polarFacet_of_supportHeight_eq_one (I : ToricInput n)
    {x : RealSpace n} (hx : supportHeight I x = 1) :
    ∃ v ∈ I.vertices, x ∈ polarFacet I v := by
  obtain ⟨v, hv⟩ := I.supportHeight_attained x
  exact ⟨v.val, v.property, hx.le, hv.trans hx⟩

end FsFltz
