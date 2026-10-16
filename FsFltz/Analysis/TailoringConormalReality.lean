import FsFltz.Analysis.TailoringBadGeometry

/-!
# Reality of face-supported conormals

Source: `geometric-part-fsf-proof.tex`, `lem:localcritical`, lines 1463–1468.
This algebraic step requires no limiting sign assertion.
-/

noncomputable section
open scoped BigOperators
namespace FsFltz
variable {n : ℕ}

private theorem exists_faceConormalCoordinate {t : Finset (Lattice n)}
    (b : Module.Basis {v // v ∈ t} ℤ (Lattice n)) (hb : ∀ v, b v = v.val)
    (w : {v // v ∈ t}) :
    ∃ L : RealSpace n →ₗ[ℝ] ℝ, ∀ v ∈ t,
      L (latticeReal v) = if v = w.val then 1 else 0 := by
  classical
  let M : Lattice n →ₗ[ℤ] ℝ := b.constr ℝ fun z => if z = w then 1 else 0
  refine ⟨realExtension M, ?_⟩
  intro v hv
  rw [realExtension_latticeReal]
  simpa only [M, hb, Subtype.ext_iff] using
    b.constr_basis ℝ (fun z => if z = w then (1 : ℝ) else 0) ⟨v, hv⟩

/-- A normalized conormal supported on a proper face is real whenever its
nonzero scalar multiple is a real vector. -/
theorem face_complex_conormal_real (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hne : s.Nonempty) (hproper : s ≠ I.vertices)
    {p : RealSpace n} (hp0 : p ≠ 0) (q : Lattice n → ℂ) (t : ℂ)
    (hsum : ∑ v ∈ s, q v = 1)
    (hp : (fun j => (p j : ℂ)) = t • ∑ v ∈ s, q v • latticeComplex v) :
    t.im = 0 ∧ t.re ≠ 0 ∧ ∀ a ∈ s, (q a).im = 0 := by
  classical
  have himag : (0 : RealSpace n) = ∑ v ∈ s, (t * q v).im • latticeReal v := by
    ext j
    have hj := congrArg (fun z : Fin n → ℂ => (z j).im) hp
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      latticeComplex, latticeReal, Complex.mul_im, add_mul, mul_assoc,
      Finset.sum_add_distrib] using hj
  obtain ⟨F, hF, hsF, b, hb⟩ := I.exists_facet_basis_containing_face hs hne hproper
  have hprod (a) (ha : a ∈ s) : (t * q a).im = 0 := by
    obtain ⟨L, hL⟩ := exists_faceConormalCoordinate b hb ⟨a, hsF ha⟩
    have hLzero := congrArg L himag
    have hLsum : L (∑ v ∈ s, (t * q v).im • latticeReal v) = (t * q a).im := by
      simp only [map_sum, map_smul, smul_eq_mul]
      calc
        ∑ v ∈ s, (t * q v).im * L (latticeReal v) =
            ∑ v ∈ s, (t * q v).im * (if v = a then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hL v (hsF hv)]
        _ = _ := by simp [ha]
    rw [map_zero, hLsum] at hLzero
    exact hLzero.symm
  have hsumprod : ∑ v ∈ s, t * q v = t := by rw [← Finset.mul_sum, hsum, mul_one]
  have htim : t.im = 0 := by
    rw [← hsumprod, Complex.im_sum]
    exact Finset.sum_eq_zero (fun a ha => hprod a ha)
  have ht0 : t ≠ 0 := by
    intro ht
    apply hp0
    ext j
    have hj := congrArg (fun z : Fin n → ℂ => (z j).re) hp
    simpa [ht] using hj
  have htre : t.re ≠ 0 := by
    intro ht
    exact ht0 (Complex.ext ht htim)
  refine ⟨htim, htre, ?_⟩
  intro a ha
  have hi := hprod a ha
  simp only [Complex.mul_im, htim, zero_mul, add_zero] at hi
  exact (mul_eq_zero.mp hi).resolve_left htre

end FsFltz
