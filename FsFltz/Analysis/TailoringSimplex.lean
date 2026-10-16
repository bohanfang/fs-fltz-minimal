import FsFltz.Analysis.TailoringCutoffs
import FsFltz.Analysis.PolarFanGeometry
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Uniform simplicial support of the literal tailoring cutoffs

Source: `geometric-part-fsf-proof.tex`, `lem:cutoffs`, lines 1072–1096.
The retained exponent set is computed from the actual all-pairs cutoffs.
The native uniform common-face tolerance yields a quantitative alternative
to the source's finite linear-programming argument: retention of a vertex
forces the ambient norm to grow at least linearly in `β`, whereas the
retention deficit grows only as `√β`. The containing facet's given integral
basis proves real affine independence of zero together with its vertices.
-/

noncomputable section

namespace FsFltz

open Set
open scoped BigOperators Topology NNReal

variable {n : ℕ}

/-- The actual exponents whose tailoring cutoff is positive. -/
def tailoringRetainedExponents (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    Finset (Lattice n) :=
  (tailoringExponents I).filter fun a => 0 < tailoringCutoff I β a u

/-- The nonzero members of the actual retained exponent set. -/
def tailoringRetainedVertices (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    Finset (Lattice n) :=
  (tailoringRetainedExponents I β u).erase 0

theorem mem_tailoringRetainedVertices_iff (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (v : Lattice n) :
    v ∈ tailoringRetainedVertices I β u ↔ v ∈ I.vertices ∧ 0 < tailoringCutoff I β v u := by
  simp only [tailoringRetainedVertices, tailoringRetainedExponents,
    Finset.mem_erase, Finset.mem_filter, tailoringExponents, Finset.mem_insert]
  constructor
  · rintro ⟨hne, h0 | hv, hr⟩
    · exact (hne h0).elim
    · exact ⟨hv, hr⟩
  · rintro ⟨hv, hr⟩
    exact ⟨fun he => I.zero_not_mem_vertices (he ▸ hv), Or.inr hv, hr⟩

theorem tailoringRetainedVertices_subset (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    tailoringRetainedVertices I β u ⊆ I.vertices :=
  fun v hv => ((mem_tailoringRetainedVertices_iff I β u v).mp hv).1

theorem tailoringRetainedExponents_subset_insert (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) :
    tailoringRetainedExponents I β u ⊆ insert 0 (tailoringRetainedVertices I β u) := by
  intro a ha
  by_cases he : a = 0
  · exact Finset.mem_insert.mpr (Or.inl he)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he, ha⟩))

/-- An explicit threshold makes the square-root deficit small relative to
the linear lower bound forced by retaining a nonconstant term. -/
theorem exists_tailoringDeficit_threshold (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      0 < β - Real.sqrt β - 2 ∧
        C * (Real.sqrt β + 2) ≤ ε * (β - Real.sqrt β - 2) := by
  let T : ℝ := 4 + 4 * C / ε
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T ^ 2, sq_pos_of_pos hT, fun β hβ => ?_⟩
  have hβpos : 0 < β := (sq_pos_of_pos hT).trans_le hβ
  have hsq := Real.sq_sqrt hβpos.le
  have hs : 0 ≤ Real.sqrt β := Real.sqrt_nonneg β
  have hTs : T ≤ Real.sqrt β := by nlinarith
  have hs4 : 4 ≤ Real.sqrt β := by
    have : 0 ≤ 4 * C / ε := by positivity
    dsimp [T] at hTs
    linarith
  have hCs : 4 * C ≤ ε * Real.sqrt β := by
    have : 4 * C / ε ≤ Real.sqrt β := by dsimp [T] at hTs; linarith
    exact (div_le_iff₀ hε).mp this |>.trans_eq (mul_comm _ _)
  have hhalf : β / 2 ≤ β - Real.sqrt β - 2 := by nlinarith
  refine ⟨(half_pos hβpos).trans_le hhalf, ?_⟩
  calc
    C * (Real.sqrt β + 2) ≤ C * (2 * Real.sqrt β) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ ≤ ε * (β / 2) := by
      have := mul_le_mul_of_nonneg_right hCs hs
      nlinarith
    _ ≤ ε * (β - Real.sqrt β - 2) := mul_le_mul_of_nonneg_left hhalf hε.le

/-- Real linear independence follows from the given integral basis by
extending its coordinate selectors to real linear forms. -/
theorem linearIndependent_latticeReal_of_basis {t : Finset (Lattice n)}
    (b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) :
    LinearIndependent ℝ (fun v : {v : Lattice n // v ∈ t} => latticeReal v.val) := by
  classical
  let f : {v : Lattice n // v ∈ t} → Module.Dual ℝ (RealSpace n) :=
    fun i => realExtension ((b.constr ℝ) (fun j => if j = i then (1 : ℝ) else 0))
  have hf (i j : {v : Lattice n // v ∈ t}) :
      f i (latticeReal j.val) = if j = i then 1 else 0 := by
    rw [realExtension_latticeReal]
    simpa only [hb] using b.constr_basis ℝ (fun j => if j = i then (1 : ℝ) else 0) j
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ f
  · intro i j hij
    rw [hf, ite_eq_right (Ne.symm hij)]
  · intro i
    rw [hf, ite_eq_left rfl]

/-- Zero and the vertices of any actual facet are the vertices of a real simplex. -/
theorem ToricInput.affineIndependent_zero_insert_facet (I : ToricInput n)
    {t : Finset (Lattice n)} (ht : IsPolytopeFacet I.vertices t) :
    AffineIndependent ℝ (fun a : {a : Lattice n // a ∈ insert 0 t} => latticeReal a.val) := by
  classical
  obtain ⟨b, hb⟩ := I.facet_basis t ht
  have hli := linearIndependent_latticeReal_of_basis b hb
  let o : {a : Lattice n // a ∈ insert 0 t} := ⟨0, Finset.mem_insert_self _ _⟩
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ o]
  let f : {a : {a : Lattice n // a ∈ insert 0 t} // a ≠ o} →
      {v : Lattice n // v ∈ t} := fun a => ⟨a.val.val, by
        rcases Finset.mem_insert.mp a.val.property with he | he
        · exact (a.property (Subtype.ext he)).elim
        · exact he⟩
  have hf : Function.Injective f := by
    intro a c h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun v : {v : Lattice n // v ∈ t} => v.val) h)
  have hz : latticeReal (0 : Lattice n) = 0 := by ext j; simp [latticeReal]
  simpa only [Function.comp_def, f, o, hz, vsub_eq_sub, sub_zero] using hli.comp f hf

/-- Actual retained vertices have a small support deficit and a large pairing. -/
theorem tailoringRetainedVertex_estimates (I : ToricInput n) (β : ℝ)
    (u : RealSpace n) (v : Lattice n) (hv : v ∈ tailoringRetainedVertices I β u) :
    supportHeight I u - pairing v u < Real.sqrt β + 2 ∧
      β - Real.sqrt β - 2 < pairing v u := by
  obtain ⟨hvV, hret⟩ := (mem_tailoringRetainedVertices_iff I β u v).mp hv
  have h := tailoringCutoff_retained_deficit I β v u hret
  rw [tailoringWeight_vertex I β ⟨v, hvV⟩] at h
  have h0 : 0 ≤ tailoringMaxWeight I β u := le_max_left _ _
  have hh : supportHeight I u - β ≤ tailoringMaxWeight I β u := le_max_right _ _
  constructor <;> linarith

/-- A single threshold places all actual retained nonzero exponents in a
nonempty proper supporting face, uniformly over the entire real ambient space. -/
theorem ToricInput.exists_tailoringRetainedVertices_face (I : ToricInput n) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ u : RealSpace n,
      ∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧ t ≠ I.vertices ∧
        tailoringRetainedVertices I β u ⊆ t := by
  obtain ⟨ε, hε, hface⟩ := I.uniform_pairingGap_face
  let C : ℝ := supportHeightLipschitzConstant I
  have hC : 0 < C := supportHeightLipschitzConstant_pos I
  obtain ⟨β₀, hβ₀, hthreshold⟩ := exists_tailoringDeficit_threshold C ε hC hε
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one I.positive_rank
  let j : Fin n := ⟨0, hn⟩
  let u₀ : RealSpace n := fun i => if i = j then 1 else 0
  have hu₀ : u₀ ≠ 0 := by
    intro he
    have := congrFun he j
    simp [u₀] at this
  refine ⟨β₀, hβ₀, fun β hβ u => ?_⟩
  rcases (tailoringRetainedVertices I β u).eq_empty_or_nonempty with he | hne
  · obtain ⟨t, ht, htne, htproper, _⟩ :=
      hface u₀ hu₀ ∅ (Finset.empty_subset _) (by simp)
    exact ⟨t, ht, htne, htproper, he ▸ Finset.empty_subset _⟩
  · obtain ⟨v, hv⟩ := hne
    have hvV := tailoringRetainedVertices_subset I β u hv
    have hvlarge := (tailoringRetainedVertex_estimates I β u v hv).2
    have hupper : supportHeight I u ≤ C * ‖u‖ := by
      simpa only [I.supportHeight_zero, sub_zero] using
        I.supportHeight_sub_le u 0
    have hnorm : β - Real.sqrt β - 2 < C * ‖u‖ :=
      hvlarge.trans_le ((I.pairing_le_supportHeight u ⟨v, hvV⟩).trans hupper)
    obtain ⟨hlarge, hsmall⟩ := hthreshold β hβ
    have hu : u ≠ 0 := by
      intro he
      rw [he, norm_zero, mul_zero] at hnorm
      linarith
    have hgap : Real.sqrt β + 2 < ε * ‖u‖ := by
      apply (mul_lt_mul_iff_right₀ hC).mp
      calc
        C * (Real.sqrt β + 2) ≤ ε * (β - Real.sqrt β - 2) := hsmall
        _ < ε * (C * ‖u‖) := mul_lt_mul_of_pos_left hnorm hε
        _ = C * (ε * ‖u‖) := by ring
    apply hface u hu _ (tailoringRetainedVertices_subset I β u)
    intro w hw
    exact ((tailoringRetainedVertex_estimates I β u w hw).1.trans hgap).le

/-- For all sufficiently large `β`, the actual retained exponents lie in
zero joined to an actual facet, whose real vertices are affinely independent.
The actual retained nonzero exponents are real linearly independent. -/
theorem ToricInput.exists_tailoringRetained_simplex (I : ToricInput n) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ u : RealSpace n,
      ∃ t, IsPolytopeFacet I.vertices t ∧
        tailoringRetainedExponents I β u ⊆ insert 0 t ∧
        AffineIndependent ℝ
          (fun a : {a : Lattice n // a ∈ insert 0 t} => latticeReal a.val) ∧
        LinearIndependent ℝ
          (fun v : {v : Lattice n // v ∈ tailoringRetainedVertices I β u} => latticeReal v.val) := by
  obtain ⟨β₀, hβ₀, hface⟩ := I.exists_tailoringRetainedVertices_face
  refine ⟨β₀, hβ₀, fun β hβ u => ?_⟩
  obtain ⟨s, hs, hsne, hsproper, hrs⟩ := hface β hβ u
  obtain ⟨t, ht, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hsne hsproper
  have hrt := hrs.trans hst
  refine ⟨t, ht, ?_, I.affineIndependent_zero_insert_facet ht, ?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp (tailoringRetainedExponents_subset_insert I β u ha) with he | he
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (hrt he))
  · let f : {v : Lattice n // v ∈ tailoringRetainedVertices I β u} →
        {v : Lattice n // v ∈ t} := fun v => ⟨v.val, hrt v.property⟩
    have hf : Function.Injective f := by
      intro v w he
      exact Subtype.ext (congrArg (fun v : {v : Lattice n // v ∈ t} => v.val) he)
    simpa only [Function.comp_def, f] using (linearIndependent_latticeReal_of_basis b hb).comp f hf

end FsFltz
