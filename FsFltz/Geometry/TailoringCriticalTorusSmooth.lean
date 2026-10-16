import FsFltz.ToricFaceTorus

/-!
# Smooth integral coordinates for the literal critical face torus

Source: `geometric-part-fsf-proof.tex`, `prop:morsebott`, lines 1529–1531,
1563–1569, and `lem:stable`, lines 1709–1725. Integral basis changes are
actual diffeomorphisms of the period-`2π` quotient torus; no global real
angles are introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FsFltz

open Set Function
open scoped Topology BigOperators ContDiff Manifold

/-- Smooth maps into the actual finite quotient-product atlas can be
assembled componentwise. -/
theorem contMDiff_torus_mk {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {n : ℕ} {f : M → Torus n}
    (h : ∀ j, ContMDiff 𝓘(ℝ, E) (𝓡 1) ∞ (fun θ => f θ j)) :
    ContMDiff 𝓘(ℝ, E) (torusModel n) ∞ f := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(continuous_pi (fun j => (h j).continuous)).continuousAt, ?_⟩
  apply contDiffWithinAt_pi.mpr
  intro j
  exact (contMDiffAt_iff.mp (h j x)).2

/-- The literal quotient-valued lattice angle pairing is smooth. -/
theorem contMDiff_integralAngle {n : ℕ} (v : Lattice n) :
    ContMDiff (torusModel n) (𝓡 1) ∞ (integralAngle v) := by
  have he : integralAngle v = angleCircleHomeomorph.symm ∘ character v := by
    funext θ
    apply angleCircleHomeomorph.injective
    rw [Function.comp_apply, Homeomorph.apply_symm_apply]
    exact angleCircleHomeomorph_eq_toCircle _
  rw [he]
  exact contMDiff_angleCircleHomeomorph_symm.comp (contMDiff_character v)

/-- Integral basis coordinates on the period-`2π` torus, with the inverse
defined by the same basis's integer-linear reconstruction. -/
def integralBasisTorusEquiv {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Torus n ≃ Torus n where
  toFun θ i := integralAngle (b i) θ
  invFun α := torusOfLatticeLinear (b.constr ℤ α)
  left_inv θ := by
    change torusOfLatticeLinear (b.constr ℤ (fun i => integralAngle (b i) θ)) = θ
    have hL : b.constr ℤ (fun i => integralAngle (b i) θ) = integralAngleLinear θ := by
      apply b.ext
      intro i
      rw [Module.Basis.constr_basis]
      rfl
    rw [hL]
    funext j
    simp [torusOfLatticeLinear, integralAngleLinear, integralAngle, Pi.basisFun_apply]
  right_inv α := by
    funext i
    change integralAngle (b i) (torusOfLatticeLinear (b.constr ℤ α)) = α i
    rw [integralAngle_torusOfLatticeLinear, Module.Basis.constr_basis]

/-- Both directions of an integral basis change are smooth quotient maps. -/
def integralBasisTorusDiffeomorph {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Diffeomorph (torusModel n) (torusModel n) (Torus n) (Torus n) ∞ where
  toEquiv := integralBasisTorusEquiv b
  contMDiff_toFun := contMDiff_torus_mk fun i => contMDiff_integralAngle (b i)
  contMDiff_invFun := by
    apply contMDiff_torus_mk
    intro j
    change ContMDiff (torusModel n) (𝓡 1) ∞
      (fun α => (b.constr ℤ α) ((Pi.basisFun ℤ (Fin n)) j))
    simp only [Module.Basis.constr_apply_fintype]
    exact contMDiff_integralAngle (fun i => b.repr ((Pi.basisFun ℤ (Fin n)) j) i)

/-- Insertion of free quotient angles with the selected active angles zero. -/
def torusCoordinateInsert {n m : ℕ} (s : Finset (Fin n))
    (e : Fin m ≃ {i : Fin n // i ∉ s}) (θ : Torus m) : Torus n :=
  fun i => if h : i ∈ s then 0 else θ (e.symm ⟨i, h⟩)

/-- Extraction of the same free quotient angles. -/
def torusCoordinateExtract {n m : ℕ} {s : Finset (Fin n)}
    (e : Fin m ≃ {i : Fin n // i ∉ s})
    (θ : Torus n) : Torus m := fun i => θ (e i).val

theorem torusCoordinateExtract_insert {n m : ℕ} (s : Finset (Fin n))
    (e : Fin m ≃ {i : Fin n // i ∉ s}) (θ : Torus m) :
    torusCoordinateExtract e (torusCoordinateInsert s e θ) = θ := by
  funext i
  simp [torusCoordinateExtract, torusCoordinateInsert, (e i).property]

theorem contMDiff_torusCoordinateInsert {n m : ℕ} (s : Finset (Fin n))
    (e : Fin m ≃ {i : Fin n // i ∉ s}) :
    ContMDiff (torusModel m) (torusModel n) ∞ (torusCoordinateInsert s e) := by
  apply contMDiff_torus_mk
  intro i
  by_cases hi : i ∈ s
  · simp only [torusCoordinateInsert, hi, dite_true]
    exact contMDiff_const
  · simp only [torusCoordinateInsert, hi, dite_false]
    exact contMDiff_torus_eval _

theorem contMDiff_torusCoordinateExtract {n m : ℕ} {s : Finset (Fin n)}
    (e : Fin m ≃ {i : Fin n // i ∉ s}) :
    ContMDiff (torusModel n) (torusModel m) ∞ (torusCoordinateExtract e) :=
  contMDiff_torus_mk fun i => contMDiff_torus_eval (e i).val

theorem range_torusCoordinateInsert {n m : ℕ} (s : Finset (Fin n))
    (e : Fin m ≃ {i : Fin n // i ∉ s}) :
    range (torusCoordinateInsert s e) = {θ | ∀ i ∈ s, θ i = 0} := by
  ext θ
  constructor
  · rintro ⟨α, rfl⟩ i hi
    simp [torusCoordinateInsert, hi]
  · intro hθ
    refine ⟨torusCoordinateExtract e θ, ?_⟩
    funext i
    by_cases hi : i ∈ s
    · simp [torusCoordinateInsert, hi, hθ i hi]
    · simp [torusCoordinateInsert, torusCoordinateExtract, hi]

/-- A smooth retraction makes the tangent injection explicit, in the actual
quotient atlas. This includes a zero-dimensional source torus. -/
theorem torus_immersion_of_smooth_leftInverse {n m : ℕ} {f : Torus m → Torus n}
    {r : Torus n → Torus m}
    (hf : ContMDiff (torusModel m) (torusModel n) ∞ f)
    (hr : ContMDiff (torusModel n) (torusModel m) ∞ r)
    (hleft : LeftInverse r f) (θ : Torus m) :
    Injective (mfderiv (torusModel m) (torusModel n) f θ) := by
  have he : r ∘ f = id := funext hleft
  have hd := mfderiv_comp θ (hr.mdifferentiable (by simp) (f θ))
    (hf.mdifferentiable (by simp) θ)
  rw [he, mfderiv_id] at hd
  intro V W hVW
  have h := congrArg (fun L : TorusCoordinates m →L[ℝ] TorusCoordinates m => L V - L W) hd
  change V - W =
    mfderiv (torusModel n) (torusModel m) r (f θ) (mfderiv (torusModel m) (torusModel n) f θ V) -
      mfderiv (torusModel n) (torusModel m) r (f θ) (mfderiv (torusModel m) (torusModel n) f θ W) at h
  rw [hVW, sub_self] at h
  exact sub_eq_zero.mp h

/-- Smoothness of the fan supplies an actual integral basis containing
every generator of a proper face. -/
theorem ToricInput.exists_indexed_basis_containing_face {n : ℕ} (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∀ v ∈ s, v ∈ range b := by
  obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hsne hsproper
  let e := b.indexEquiv (Pi.basisFun ℤ (Fin n))
  refine ⟨b.reindex e, ?_⟩
  intro v hv
  refine ⟨e ⟨v, hst hv⟩, ?_⟩
  simpa only [Module.Basis.reindex_apply, Equiv.symm_apply_apply] using hb ⟨v, hst hv⟩

/-- A subset of an integral basis has exactly the expected number of
active angle coordinates. -/
theorem card_basis_active_indices {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) (hs : ∀ v ∈ s, v ∈ range b) :
    (Finset.univ.filter fun i => b i ∈ s).card = s.card := by
  classical
  apply Finset.card_bij (fun i _ => b i)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    exact b.injective hij
  · intro v hv
    obtain ⟨i, rfl⟩ := hs v hv
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

/-- The literal critical face torus is the image of an actual smooth
embedded immersion of the dimension prescribed by the face. A global
smooth retraction is constructed at the same time. -/
theorem ToricInput.exists_smooth_coneTorus_parametrization {n : ℕ} (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hsne : s.Nonempty) (hsproper : s ≠ I.vertices) :
    ∃ (f : Torus (n - s.card) → Torus n) (r : Torus n → Torus (n - s.card)),
      ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f ∧
      ContMDiff (torusModel n) (torusModel (n - s.card)) ∞ r ∧
      LeftInverse r f ∧ Topology.IsEmbedding f ∧
      (∀ θ, Injective (mfderiv (torusModel (n - s.card)) (torusModel n) f θ)) ∧
      range f = coneTorus (positiveCone s) := by
  classical
  obtain ⟨b, hb⟩ := I.exists_indexed_basis_containing_face hs hsne hsproper
  let J := Finset.univ.filter fun i => b i ∈ s
  have hJ : J.card = s.card := card_basis_active_indices b s hb
  have hfree : Fintype.card (Fin (n - s.card)) = Fintype.card {i : Fin n // i ∉ J} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hJ,
      Fintype.card_fin]
  let e : Fin (n - s.card) ≃ {i : Fin n // i ∉ J} := Fintype.equivOfCardEq hfree
  let d := integralBasisTorusDiffeomorph b
  let f : Torus (n - s.card) → Torus n := d.symm ∘ torusCoordinateInsert J e
  let r : Torus n → Torus (n - s.card) := torusCoordinateExtract e ∘ d
  have hf : ContMDiff (torusModel (n - s.card)) (torusModel n) ∞ f :=
    d.symm.contMDiff.comp (contMDiff_torusCoordinateInsert J e)
  have hr : ContMDiff (torusModel n) (torusModel (n - s.card)) ∞ r :=
    (contMDiff_torusCoordinateExtract e).comp d.contMDiff
  have hleft : LeftInverse r f := by
    intro θ
    simp only [r, f, Function.comp_apply, Diffeomorph.apply_symm_apply,
      torusCoordinateExtract_insert]
  refine ⟨f, r, hf, hr, hleft,
    Topology.IsEmbedding.of_leftInverse hleft hr.continuous hf.continuous,
    torus_immersion_of_smooth_leftInverse hf hr hleft, ?_⟩
  have hcoords (θ : Torus n) : (∀ i ∈ J, d θ i = 0) ↔
      θ ∈ coneTorus (positiveCone s) := by
    rw [I.mem_coneTorus_positiveCone_iff_integralAngle hs hsne hsproper]
    constructor
    · intro h v hv
      obtain ⟨i, rfl⟩ := hb v hv
      exact h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩)
    · intro h i hi
      exact h (b i) (Finset.mem_filter.mp hi).2
  ext θ
  rw [← hcoords θ]
  constructor
  · rintro ⟨α, rfl⟩
    change ∀ i ∈ J, d (d.symm (torusCoordinateInsert J e α)) i = 0
    rw [Diffeomorph.apply_symm_apply]
    intro i hi
    simp [torusCoordinateInsert, hi]
  · intro hθ
    have hmem : d θ ∈ range (torusCoordinateInsert J e) := by
      rw [range_torusCoordinateInsert]
      exact hθ
    obtain ⟨α, hα⟩ := hmem
    refine ⟨α, ?_⟩
    change d.symm (torusCoordinateInsert J e α) = θ
    rw [hα, Diffeomorph.symm_apply_apply]

end FsFltz
