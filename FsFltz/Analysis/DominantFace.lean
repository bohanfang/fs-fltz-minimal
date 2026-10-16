import FsFltz.Analytic
import FsFltz.Analysis.FiniteSupportGrowth
import FsFltz.Analysis.MonomialTail
import FsFltz.ToricFanSmoothness
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Noncancellation on the proper faces of the toric support

Source: `geometric-part-fsf-proof.tex`, `lem:dominant`, lines 688–709,
and `geoemtric-part-fsf.tex`, `sec:data`, lines 57–71. The input's integral
facet bases provide coefficient extraction for complex linear combinations
of proper-face vertices. Finiteness gives one positive lower bound for all
these faces. A compact unit-sphere argument for finite pairing deficits
constructs the dominant face, and the complementary monomials are bounded
using their exponential deficits. Together these prove derivative dominance
for each original finite input, with the prescribed Euclidean norm. Uniform
coefficient-path estimates and geometric critical-point realization remain
separate obligations.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators

variable {n : ℕ}

/-- Scalar extension of an input lattice vertex to the complex coordinates. -/
def latticeComplex (v : Lattice n) : Fin n → ℂ := fun j => (v j : ℂ)

/-- The complex linear combination of the vertices of a finite support. -/
def complexVertexSum (s : Finset (Lattice n))
    (γ : {v : Lattice n // v ∈ s} → ℂ) : Fin n → ℂ :=
  ∑ v, γ v • latticeComplex v.val

/-- The linear map underlying the finite vertex sum. -/
def complexVertexSumLinearMap (s : Finset (Lattice n)) :
    ({v : Lattice n // v ∈ s} → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun := complexVertexSum s
  map_add' γ δ := by
    simp only [complexVertexSum, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c γ := by
    simp [complexVertexSum, smul_smul, Finset.smul_sum, smul_eq_mul]

/-- Extend an integral linear functional to the complex coordinate space. -/
def complexExtension (L : Lattice n →ₗ[ℤ] ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (Pi.basisFun ℂ (Fin n)).constr ℂ fun j => L ((Pi.basisFun ℤ (Fin n)) j)

/-- The extension agrees with the integral functional on every lattice
vector, so it applies to the actual facet basis rather than a replacement. -/
@[simp]
theorem complexExtension_latticeComplex (L : Lattice n →ₗ[ℤ] ℂ) (v : Lattice n) :
    complexExtension L (latticeComplex v) = L v := by
  rw [← (Pi.basisFun ℂ (Fin n)).sum_repr (latticeComplex v)]
  simp only [map_sum, map_smul, complexExtension, Module.Basis.constr_basis,
    Pi.basisFun_repr, latticeComplex, smul_eq_mul]
  have h := congrArg L ((Pi.basisFun ℤ (Fin n)).sum_repr v)
  simp only [map_sum, map_smul, Pi.basisFun_repr] at h
  simpa only [zsmul_eq_mul] using h

/-- A containing integral basis supplies a complex-linear functional
extracting each coefficient of a proper-face combination. -/
theorem complexVertexSum_coefficient {s t : Finset (Lattice n)}
    (hst : s ⊆ t) (b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) (v : {v : Lattice n // v ∈ s}) :
    ∃ L : (Fin n → ℂ) →ₗ[ℂ] ℂ, ∀ γ, L (complexVertexSum s γ) = γ v := by
  classical
  let i : {v : Lattice n // v ∈ t} := ⟨v.val, hst v.property⟩
  let L : Lattice n →ₗ[ℤ] ℂ := b.constr ℂ fun w => if w = i then 1 else 0
  have hL (w : {v : Lattice n // v ∈ s}) :
      L w.val = if w = v then 1 else 0 := by
    rw [← hb ⟨w.val, hst w.property⟩]
    change (b.constr ℂ (fun w => if w = i then 1 else 0))
      (b ⟨w.val, hst w.property⟩) = _
    rw [b.constr_basis]
    have he : (⟨w.val, hst w.property⟩ : {v : Lattice n // v ∈ t}) = i ↔ w = v := by
      simp only [i, Subtype.ext_iff]
    simp only [he]
  refine ⟨complexExtension L, ?_⟩
  intro γ
  simp [complexVertexSum, map_sum, map_smul, hL, smul_eq_mul]

/-- Complex coefficients cannot cancel on a subset of an actual integral
facet basis. This proves injectivity after scalar extension to `ℂ`. -/
theorem complexVertexSumLinearMap_injective_of_basis {s t : Finset (Lattice n)}
    (hst : s ⊆ t) (b : Module.Basis {v : Lattice n // v ∈ t} ℤ (Lattice n))
    (hb : ∀ v, b v = v.val) : Function.Injective (complexVertexSumLinearMap s) := by
  intro γ δ he
  funext v
  obtain ⟨L, hL⟩ := complexVertexSum_coefficient hst b hb v
  exact (hL γ).symm.trans ((congrArg L he).trans (hL δ))

/-- Every proper nonempty input face is independent over the complex numbers
in the precise finite-sum form needed for the derivative estimate. -/
theorem ToricInput.complexVertexSumLinearMap_injective (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hne : s.Nonempty) (hproper : s ≠ I.vertices) :
    Function.Injective (complexVertexSumLinearMap s) := by
  obtain ⟨t, _, hst, b, hb⟩ := I.exists_facet_basis_containing_face hs hne hproper
  exact complexVertexSumLinearMap_injective_of_basis hst b hb

/-- A positive quantitative noncancellation bound for any fixed proper
nonempty face, obtained from finite-dimensional injectivity. -/
theorem ToricInput.complex_face_lowerBound (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : IsPolytopeFace I.vertices s)
    (hne : s.Nonempty) (hproper : s ≠ I.vertices) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : {v : Lattice n // v ∈ s} → ℂ,
      c * ‖γ‖ ≤ ‖complexVertexSum s γ‖ := by
  obtain ⟨K, hK, hanti⟩ := (complexVertexSumLinearMap s).injective_iff_antilipschitz.mp
    (I.complexVertexSumLinearMap_injective hs hne hproper)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hKreal, ?_⟩
  intro γ
  have hb := ZeroHomClass.bound_of_antilipschitz (complexVertexSumLinearMap s) hanti γ
  calc
    (K : ℝ)⁻¹ * ‖γ‖ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖complexVertexSum s γ‖) :=
      mul_le_mul_of_nonneg_left hb (inv_pos.mpr hKreal).le
    _ = ‖complexVertexSum s γ‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKreal), one_mul]

/-- One positive noncancellation constant works for every proper nonempty
face of the actual finite toric support. The norms here are the supremum
norms of the coordinate function spaces. -/
theorem ToricInput.uniform_complex_face_lowerBound (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∀ s, IsPolytopeFace I.vertices s → s.Nonempty →
      s ≠ I.vertices → ∀ γ : {v : Lattice n // v ∈ s} → ℂ,
        c * ‖γ‖ ≤ ‖complexVertexSum s γ‖ := by
  classical
  let P (s : Finset (Lattice n)) :=
    IsPolytopeFace I.vertices s ∧ s.Nonempty ∧ s ≠ I.vertices
  have hex : ∀ s : Finset (Lattice n), ∃ C : ℝ, 0 < C ∧
      (P s → ∀ γ : {v : Lattice n // v ∈ s} → ℂ,
        ‖γ‖ ≤ C * ‖complexVertexSum s γ‖) := by
    intro s
    by_cases hs : P s
    · obtain ⟨K, hK, hanti⟩ := (complexVertexSumLinearMap s).injective_iff_antilipschitz.mp
        (I.complexVertexSumLinearMap_injective hs.1 hs.2.1 hs.2.2)
      exact ⟨K, by exact_mod_cast hK,
        fun _ γ => ZeroHomClass.bound_of_antilipschitz
          (complexVertexSumLinearMap s) hanti γ⟩
    · exact ⟨1, zero_lt_one, fun hs' => (hs hs').elim⟩
  choose C hC hbound using hex
  let B : ℝ := 1 + ∑ s ∈ I.vertices.powerset, C s
  have hsum : 0 ≤ ∑ s ∈ I.vertices.powerset, C s :=
    Finset.sum_nonneg fun s _ => (hC s).le
  have hB : 0 < B := by dsimp [B]; linarith
  refine ⟨B⁻¹, inv_pos.mpr hB, ?_⟩
  intro s hs hne hproper γ
  have hsB : C s ≤ B := by
    have hc := Finset.single_le_sum (fun t (_ : t ∈ I.vertices.powerset) => (hC t).le)
      (Finset.mem_powerset.mpr hs.1)
    dsimp [B]
    linarith
  have hb : ‖γ‖ ≤ B * ‖complexVertexSum s γ‖ :=
    (hbound s ⟨hs, hne, hproper⟩ γ).trans
      (mul_le_mul_of_nonneg_right hsB (norm_nonneg _))
  calc
    B⁻¹ * ‖γ‖ ≤ B⁻¹ * (B * ‖complexVertexSum s γ‖) :=
      mul_le_mul_of_nonneg_left hb (inv_pos.mpr hB).le
    _ = ‖complexVertexSum s γ‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hB), one_mul]

/-- The supremum norm of the literal derivative is bounded by its source
Euclidean norm, expressed using the already defined scalar `a = ḠᵀG`. -/
theorem norm_G_le_sqrt_a (I : ToricInput n) (y : LGSpace n) :
    ‖G I y‖ ≤ Real.sqrt (a I y) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  apply Real.le_sqrt_of_sq_le
  rw [Complex.sq_norm]
  exact Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (G I y k))
    (Finset.mem_univ j)

/-- The derivative sum restricted to the actual vertices of a face.
The coefficients are inherited from `I`, without a new coefficient choice. -/
def faceMonomialDerivative (I : ToricInput n) (s : Finset (Lattice n))
    (hs : s ⊆ I.vertices) (y : LGSpace n) : Fin n → ℂ :=
  complexVertexSum s (fun v => monomial (I.coeff ⟨v.val, hs v.property⟩) v.val y)

/-- Coordinate formula for the literal partial sum, used to estimate its
complement in the full derivative. -/
theorem faceMonomialDerivative_apply (I : ToricInput n) (s : Finset (Lattice n))
    (hs : s ⊆ I.vertices) (y : LGSpace n) (j : Fin n) :
    faceMonomialDerivative I s hs y j =
      ∑ v : {v : Lattice n // v ∈ s},
        monomial (I.coeff ⟨v.val, hs v.property⟩) v.val y * (v.val j : ℂ) := by
  simp [faceMonomialDerivative, complexVertexSum, latticeComplex,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The uniform face bound directly controls the literal Euclidean
derivative once a maximizing monomial lies on that face and the complementary
sum is sufficiently small. The two hypotheses isolate the pending
concentration-at-infinity argument, without assuming derivative dominance. -/
theorem ToricInput.G_lowerBound_of_face_tail (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∀ s (hs : IsPolytopeFace I.vertices s),
      s.Nonempty → s ≠ I.vertices → ∀ y : LGSpace n,
      (∃ v : {v : Lattice n // v ∈ s},
        ‖monomial (I.coeff ⟨v.val, hs.1 v.property⟩) v.val y‖ =
          maxMonomialMagnitude I y) →
      ‖G I y - faceMonomialDerivative I s hs.1 y‖ ≤ c * maxMonomialMagnitude I y →
      c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y) := by
  obtain ⟨c, hc, hface⟩ := I.uniform_complex_face_lowerBound
  refine ⟨c / 2, half_pos hc, ?_⟩
  intro s hs hne hproper y hmax htail
  let γ : {v : Lattice n // v ∈ s} → ℂ :=
    fun v => monomial (I.coeff ⟨v.val, hs.1 v.property⟩) v.val y
  obtain ⟨v, hv⟩ := hmax
  have hcoeff : maxMonomialMagnitude I y ≤ ‖γ‖ := by
    rw [← hv]
    exact norm_le_pi_norm γ v
  have hlower : c * maxMonomialMagnitude I y ≤
      ‖faceMonomialDerivative I s hs.1 y‖ :=
    (mul_le_mul_of_nonneg_left hcoeff hc.le).trans (hface s hs hne hproper γ)
  have htriangle := norm_le_insert (G I y) (faceMonomialDerivative I s hs.1 y)
  have hG : c / 2 * maxMonomialMagnitude I y ≤ ‖G I y‖ := by
    linarith
  exact hG.trans (norm_G_le_sqrt_a I y)

/-- The vertices maximizing the pairing in a prescribed radial direction. -/
def maximizingVertexFace (I : ToricInput n) (u : RealSpace n) :
    Finset (Lattice n) := by
  classical
  exact I.vertices.filter fun v => pairing v u = supportHeight I u

@[simp]
theorem mem_maximizingVertexFace (I : ToricInput n) (u : RealSpace n) (v : Lattice n) :
    v ∈ maximizingVertexFace I u ↔ v ∈ I.vertices ∧ pairing v u = supportHeight I u := by
  classical
  simp [maximizingVertexFace]

/-- Maximizing vertices always form a nonempty exposed face of the actual
input polytope. -/
theorem ToricInput.maximizingVertexFace_isPolytopeFace (I : ToricInput n)
    (u : RealSpace n) :
    IsPolytopeFace I.vertices (maximizingVertexFace I u) ∧
      (maximizingVertexFace I u).Nonempty := by
  classical
  let L : RealSpace n →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ j, x j * u j
      map_add' := by intros; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.mul_sum, mul_assoc] }
  have hL (v : Lattice n) : L (latticeReal v) = pairing v u := rfl
  refine ⟨⟨?_, L, supportHeight I u, ?_, ?_⟩, ?_⟩
  · intro v hv
    exact (mem_maximizingVertexFace I u v).mp hv |>.1
  · intro v hv
    exact I.pairing_le_supportHeight u ⟨v, hv⟩
  · intro v hv
    simp only [mem_maximizingVertexFace, hv, true_and, hL]
  · obtain ⟨v, hv⟩ := I.supportHeight_attained u
    exact ⟨v.val, (mem_maximizingVertexFace I u v.val).mpr ⟨v.property, hv⟩⟩

private theorem euclidean_radius_pos {u : RealSpace n} (hu : u ≠ 0) :
    0 < Real.sqrt (realSquaredNorm u) := by
  have hex : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨j, hj⟩ := hex
  apply Real.sqrt_pos.mpr
  exact Finset.sum_pos' (fun k _ => sq_nonneg (u k))
    ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩

/-- A nonzero radial direction exposes a proper face. Interior containment
provides vertices with strictly positive and strictly negative pairings. -/
theorem ToricInput.maximizingVertexFace_ne_vertices (I : ToricInput n)
    {u : RealSpace n} (hu : u ≠ 0) : maximizingVertexFace I u ≠ I.vertices := by
  intro he
  obtain ⟨c, hc, hpair⟩ := I.exists_pairing_ge_euclidean
  obtain ⟨v, hv, hvpair⟩ := hpair u
  obtain ⟨w, hw, hwpair⟩ := hpair (-u)
  have hr := euclidean_radius_pos hu
  have hvpos : 0 < pairing v u := (mul_pos hc hr).trans_le hvpair
  have hwpos : 0 < pairing w (-u) := by
    have hnr : realSquaredNorm (-u) = realSquaredNorm u := by
      simp [realSquaredNorm]
    rw [hnr] at hwpair
    exact (mul_pos hc hr).trans_le hwpair
  have hveq := ((mem_maximizingVertexFace I u v).mp (he.symm ▸ hv)).2
  have hweq := ((mem_maximizingVertexFace I u w).mp (he.symm ▸ hw)).2
  have hwneg : pairing w (-u) = -pairing w u := by
    simp [pairing, Finset.sum_neg_distrib]
  rw [hwneg, hweq, ← hveq] at hwpos
  linarith

/-- The sum of positive pairing deficits for a finite subset of the
vertices. It vanishes exactly when every member is a pairing maximizer. -/
def totalPairingDeficit (I : ToricInput n) (s : Finset (Lattice n))
    (u : RealSpace n) : ℝ :=
  ∑ v ∈ s, ∑ w ∈ I.vertices, max (pairing w u - pairing v u) 0

theorem totalPairingDeficit_nonneg (I : ToricInput n) (s : Finset (Lattice n))
    (u : RealSpace n) : 0 ≤ totalPairingDeficit I s u := by
  exact Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => le_max_right _ _

theorem continuous_totalPairingDeficit (I : ToricInput n) (s : Finset (Lattice n)) :
    Continuous (totalPairingDeficit I s) := by
  unfold totalPairingDeficit pairing
  fun_prop

/-- A subset not contained in any proper nonempty face has strictly
positive pairing deficit in every nonzero direction. -/
theorem ToricInput.totalPairingDeficit_pos (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices)
    (hbad : ¬∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧
      t ≠ I.vertices ∧ s ⊆ t) {u : RealSpace n} (hu : u ≠ 0) :
    0 < totalPairingDeficit I s u := by
  by_contra h
  have hz : totalPairingDeficit I s u = 0 :=
    le_antisymm (le_of_not_gt h) (totalPairingDeficit_nonneg I s u)
  have houter := (Finset.sum_eq_zero_iff_of_nonneg
    (fun v (_ : v ∈ s) => Finset.sum_nonneg
      (fun w (_ : w ∈ I.vertices) => le_max_right (pairing w u - pairing v u) 0))).mp hz
  have hsub : s ⊆ maximizingVertexFace I u := by
    intro v hv
    have hinner := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w (_ : w ∈ I.vertices) => le_max_right (pairing w u - pairing v u) 0)).mp
        (houter v hv)
    obtain ⟨w, hw⟩ := I.supportHeight_attained u
    have hgap : pairing w.val u - pairing v u ≤ 0 := by
      have hmax := le_max_left (pairing w.val u - pairing v u) 0
      rw [hinner w.val w.property] at hmax
      exact hmax
    refine (mem_maximizingVertexFace I u v).mpr ⟨hs hv, ?_⟩
    exact le_antisymm (I.pairing_le_supportHeight u ⟨v, hs hv⟩) (by rw [hw] at hgap; linarith)
  obtain ⟨hface, hne⟩ := I.maximizingVertexFace_isPolytopeFace u
  exact hbad ⟨maximizingVertexFace I u, hface, hne,
    I.maximizingVertexFace_ne_vertices hu, hsub⟩

theorem pairing_smul_real (v : Lattice n) (r : ℝ) (u : RealSpace n) :
    pairing v (r • u) = r * pairing v u := by
  simp [pairing, Finset.mul_sum, mul_left_comm]

theorem totalPairingDeficit_smul (I : ToricInput n) (s : Finset (Lattice n))
    {r : ℝ} (hr : 0 ≤ r) (u : RealSpace n) :
    totalPairingDeficit I s (r • u) = r * totalPairingDeficit I s u := by
  have hm (x : ℝ) : max (r * x) 0 = r * max x 0 := by
    rw [mul_max_of_nonneg _ _ hr, mul_zero]
  simp only [totalPairingDeficit, pairing_smul_real, ← mul_sub, hm, Finset.mul_sum]

/-- Compactness of the unit sphere turns the strict deficit of any subset
not lying in a proper face into a positive linear bound on all directions. -/
theorem ToricInput.totalPairingDeficit_lowerBound (I : ToricInput n)
    {s : Finset (Lattice n)} (hs : s ⊆ I.vertices)
    (hbad : ¬∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧
      t ≠ I.vertices ∧ s ⊆ t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : RealSpace n, δ * ‖u‖ ≤ totalPairingDeficit I s u := by
  let S := Metric.sphere (0 : RealSpace n) 1
  by_cases hne : S.Nonempty
  · obtain ⟨ξ, hξ, hmin⟩ := (isCompact_sphere (0 : RealSpace n) 1).exists_isMinOn hne
      (continuous_totalPairingDeficit I s).continuousOn
    have hξnorm : ‖ξ‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using hξ
    have hξne : ξ ≠ 0 := by intro he; simp [he] at hξnorm
    refine ⟨totalPairingDeficit I s ξ, I.totalPairingDeficit_pos hs hbad hξne, ?_⟩
    intro u
    by_cases hu : u = 0
    · simp only [hu, norm_zero, mul_zero]
      exact totalPairingDeficit_nonneg I s 0
    let η : RealSpace n := ‖u‖⁻¹ • u
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hηnorm : ‖η‖ = 1 := by
      simp [η, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hunorm).le,
        inv_mul_cancel₀ (ne_of_gt hunorm)]
    have hη : η ∈ S := by simpa [S, Metric.mem_sphere, dist_zero_right] using hηnorm
    have hscale : ‖u‖ • η = u := by
      dsimp [η]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hunorm), one_smul]
    calc
      totalPairingDeficit I s ξ * ‖u‖ ≤ totalPairingDeficit I s η * ‖u‖ :=
        mul_le_mul_of_nonneg_right (hmin hη) hunorm.le
      _ = totalPairingDeficit I s u := by
        rw [mul_comm, ← totalPairingDeficit_smul I s hunorm.le η, hscale]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro u
    by_cases hu : u = 0
    · simp only [hu, norm_zero, mul_zero]
      exact totalPairingDeficit_nonneg I s 0
    have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hηnorm : ‖‖u‖⁻¹ • u‖ = 1 := by
      simp [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hunorm).le,
        inv_mul_cancel₀ (ne_of_gt hunorm)]
    exact (hne ⟨‖u‖⁻¹ • u,
      by simpa [S, Metric.mem_sphere, dist_zero_right] using hηnorm⟩).elim

/-- One positive linear deficit bound works for all vertex subsets that
are not contained in a proper nonempty face. -/
theorem ToricInput.uniform_totalPairingDeficit_lowerBound (I : ToricInput n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s, s ⊆ I.vertices →
      (¬∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧
        t ≠ I.vertices ∧ s ⊆ t) → ∀ u : RealSpace n,
      δ * ‖u‖ ≤ totalPairingDeficit I s u := by
  classical
  let P (s : Finset (Lattice n)) := s ⊆ I.vertices ∧
    ¬∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧ t ≠ I.vertices ∧ s ⊆ t
  have hex : ∀ s : Finset (Lattice n), ∃ δ : ℝ, 0 < δ ∧
      (P s → ∀ u : RealSpace n, δ * ‖u‖ ≤ totalPairingDeficit I s u) := by
    intro s
    by_cases hs : P s
    · obtain ⟨δ, hδ, hb⟩ := I.totalPairingDeficit_lowerBound hs.1 hs.2
      exact ⟨δ, hδ, fun _ => hb⟩
    · exact ⟨1, zero_lt_one, fun hs' => (hs hs').elim⟩
  choose δ hδ hbound using hex
  obtain ⟨s₀, hs₀, hmin⟩ := I.vertices.powerset.exists_min_image δ
    (Finset.powerset_nonempty I.vertices)
  refine ⟨δ s₀, hδ s₀, ?_⟩
  intro s hs hbad u
  exact (mul_le_mul_of_nonneg_right
    (hmin s (Finset.mem_powerset.mpr hs)) (norm_nonneg u)).trans
      (hbound s ⟨hs, hbad⟩ u)

/-- Any subset whose vertices are uniformly close to the largest pairing
lies in one proper face. The tolerance is independent of the direction. -/
theorem ToricInput.uniform_pairingGap_face (I : ToricInput n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : RealSpace n, u ≠ 0 →
      ∀ s, s ⊆ I.vertices →
      (∀ v ∈ s, supportHeight I u - pairing v u ≤ ε * ‖u‖) →
      ∃ t, IsPolytopeFace I.vertices t ∧ t.Nonempty ∧ t ≠ I.vertices ∧ s ⊆ t := by
  classical
  obtain ⟨δ, hδ, hdeficit⟩ := I.uniform_totalPairingDeficit_lowerBound
  let N : ℝ := I.vertices.card
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let ε : ℝ := δ / (2 * (N ^ 2 + 1))
  have hden : 0 < 2 * (N ^ 2 + 1) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  refine ⟨ε, hε, ?_⟩
  intro u hu s hs hgap
  by_contra hbad
  have hlower := hdeficit s hs hbad u
  have hterm (v : Lattice n) (hv : v ∈ s) (w : Lattice n) (hw : w ∈ I.vertices) :
      max (pairing w u - pairing v u) 0 ≤ ε * ‖u‖ := by
    apply max_le
    · have hwle := I.pairing_le_supportHeight u ⟨w, hw⟩
      linarith [hgap v hv]
    · exact mul_nonneg hε.le (norm_nonneg _)
  have hupper : totalPairingDeficit I s u ≤ N ^ 2 * (ε * ‖u‖) := by
    calc
      totalPairingDeficit I s u ≤ ∑ _v ∈ s, ∑ _w ∈ I.vertices, ε * ‖u‖ :=
        Finset.sum_le_sum fun v hv => Finset.sum_le_sum fun w hw => hterm v hv w hw
      _ = (s.card : ℝ) * N * (ε * ‖u‖) := by
        simp only [Finset.sum_const, nsmul_eq_mul, N]
        ring
      _ ≤ N ^ 2 * (ε * ‖u‖) := by
        have hcard : (s.card : ℝ) ≤ N := by
          dsimp [N]
          exact_mod_cast Finset.card_le_card hs
        gcongr
        nlinarith
  have hsmall : N ^ 2 * ε < δ := by
    have he : ε * (2 * (N ^ 2 + 1)) = δ := div_mul_cancel₀ δ (ne_of_gt hden)
    nlinarith
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hstrict := mul_lt_mul_of_pos_right hsmall hunorm
  nlinarith

private def extendedMonomial (I : ToricInput n) (y : LGSpace n)
    (v : Lattice n) : ℂ :=
  if hv : v ∈ I.vertices then monomial (I.coeff ⟨v, hv⟩) v y else 0

private theorem extendedMonomial_eq (I : ToricInput n) (y : LGSpace n)
    (v : Lattice n) (hv : v ∈ I.vertices) :
    extendedMonomial I y v = monomial (I.coeff ⟨v, hv⟩) v y := by
  simp [extendedMonomial, hv]

private theorem G_eq_vertex_sum (I : ToricInput n) (y : LGSpace n) :
    G I y = ∑ v ∈ I.vertices, extendedMonomial I y v • latticeComplex v := by
  have hterms (v : {v : Lattice n // v ∈ I.vertices}) :
      monomial (I.coeff v) v.val y • latticeComplex v.val =
        extendedMonomial I y v.val • latticeComplex v.val := by
    rw [extendedMonomial_eq I y v.val v.property]
  calc
    G I y = complexVertexSum I.vertices (fun v => monomial (I.coeff v) v.val y) := by
      ext j
      simp [G, complexVertexSum, latticeComplex, Finset.sum_apply, smul_eq_mul]
    _ = ∑ v : {v : Lattice n // v ∈ I.vertices},
        extendedMonomial I y v.val • latticeComplex v.val := by
      simp only [complexVertexSum, hterms]
    _ = _ := Finset.sum_coe_sort I.vertices
      (fun v => extendedMonomial I y v • latticeComplex v)

private theorem faceMonomialDerivative_eq_vertex_sum (I : ToricInput n)
    (s : Finset (Lattice n)) (hs : s ⊆ I.vertices) (y : LGSpace n) :
    faceMonomialDerivative I s hs y =
      ∑ v ∈ s, extendedMonomial I y v • latticeComplex v := by
  have hterms (v : {v : Lattice n // v ∈ s}) :
      monomial (I.coeff ⟨v.val, hs v.property⟩) v.val y • latticeComplex v.val =
        extendedMonomial I y v.val • latticeComplex v.val := by
    rw [extendedMonomial_eq I y v.val (hs v.property)]
  simp only [faceMonomialDerivative, complexVertexSum, hterms]
  exact Finset.sum_coe_sort s (fun v => extendedMonomial I y v • latticeComplex v)

/-- Bounding every off-face monomial relative to the largest magnitude
bounds the actual complementary derivative sum. -/
theorem norm_G_sub_faceMonomialDerivative_le (I : ToricInput n)
    (s : Finset (Lattice n)) (hs : s ⊆ I.vertices) (y : LGSpace n)
    {ε : ℝ} (hε : 0 ≤ ε)
    (htail : ∀ v : {v : Lattice n // v ∈ I.vertices}, v.val ∉ s →
      ‖monomial (I.coeff v) v.val y‖ ≤ ε * maxMonomialMagnitude I y) :
    ‖G I y - faceMonomialDerivative I s hs y‖ ≤
      ε * maxMonomialMagnitude I y * (∑ v ∈ I.vertices, ‖latticeComplex v‖) := by
  classical
  rw [G_eq_vertex_sum, faceMonomialDerivative_eq_vertex_sum,
    ← Finset.sum_sdiff_eq_sub hs]
  calc
    ‖∑ v ∈ I.vertices \ s, extendedMonomial I y v • latticeComplex v‖ ≤
        ∑ v ∈ I.vertices \ s, ‖extendedMonomial I y v • latticeComplex v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ v ∈ I.vertices \ s, ε * maxMonomialMagnitude I y * ‖latticeComplex v‖ := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨hvV, hvs⟩ := Finset.mem_sdiff.mp hv
      rw [norm_smul, extendedMonomial_eq I y v hvV]
      exact mul_le_mul_of_nonneg_right (htail ⟨v, hvV⟩ hvs) (norm_nonneg _)
    _ ≤ ∑ v ∈ I.vertices, ε * maxMonomialMagnitude I y * ‖latticeComplex v‖ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun v _ _ => mul_nonneg
          (mul_nonneg hε (I.maxMonomialMagnitude_pos y).le) (norm_nonneg _))
    _ = _ := by rw [Finset.mul_sum]

/-- Outside a compact radial cylinder all monomials exceeding any chosen
fraction of the largest magnitude lie in one proper face. That face also
contains a maximizing monomial. Both conclusions are derived from the
literal coefficients, uniformly over the quotient torus. -/
theorem ToricInput.monomial_face_concentration (I : ToricInput n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ y : LGSpace n, L ≤ ‖y.1‖ →
      ∃ s, ∃ hs : IsPolytopeFace I.vertices s,
        s.Nonempty ∧ s ≠ I.vertices ∧
        (∃ v : {v : Lattice n // v ∈ s},
          ‖monomial (I.coeff ⟨v.val, hs.1 v.property⟩) v.val y‖ =
            maxMonomialMagnitude I y) ∧
        (∀ v : {v : Lattice n // v ∈ I.vertices}, v.val ∉ s →
          ‖monomial (I.coeff v) v.val y‖ ≤ ε * maxMonomialMagnitude I y) := by
  classical
  let q : ℝ := min ε (1 / 2)
  have hq : 0 < q := lt_min hε (by norm_num)
  obtain ⟨D, hD, hcutoff⟩ := I.exists_monomial_tail_cutoff hq
  obtain ⟨δ, hδ, hface⟩ := I.uniform_pairingGap_face
  let L : ℝ := 1 + D / δ
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro y hy
  have hunorm : 0 < ‖y.1‖ := hL.trans_le hy
  have hu : y.1 ≠ 0 := norm_pos_iff.mp hunorm
  have hgapnorm : D ≤ δ * ‖y.1‖ := by
    have hdiv : D / δ ≤ ‖y.1‖ := by dsimp [L] at hy; linarith
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hdiv
  let t := I.vertices.filter (fun v => supportHeight I y.1 - pairing v y.1 ≤ D)
  have htV : t ⊆ I.vertices := Finset.filter_subset _ _
  have htgap : ∀ v ∈ t, supportHeight I y.1 - pairing v y.1 ≤ δ * ‖y.1‖ := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2.trans hgapnorm
  obtain ⟨s, hs, hsne, hsproper, hts⟩ := hface y.1 hu t htV htgap
  have htail : ∀ v : {v : Lattice n // v ∈ I.vertices}, v.val ∉ s →
      ‖monomial (I.coeff v) v.val y‖ ≤ q * maxMonomialMagnitude I y := by
    intro v hvs
    have hvt : v.val ∉ t := fun hv => hvs (hts hv)
    have hdef : D < supportHeight I y.1 - pairing v.val y.1 := by
      have hn : ¬supportHeight I y.1 - pairing v.val y.1 ≤ D := by
        intro he
        exact hvt (Finset.mem_filter.mpr ⟨v.property, he⟩)
      exact lt_of_not_ge hn
    exact hcutoff y v hdef.le
  refine ⟨s, hs, hsne, hsproper, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := I.maxMonomialMagnitude_attained y
    have hvs : v.val ∈ s := by
      by_contra hvs
      have ht := htail v hvs
      rw [hv] at ht
      have hqhalf : q ≤ 1 / 2 := min_le_right _ _
      have hqM := mul_le_mul_of_nonneg_right hqhalf (I.maxMonomialMagnitude_pos y).le
      linarith [I.maxMonomialMagnitude_pos y]
    exact ⟨⟨v.val, hvs⟩, hv⟩
  · intro v hvs
    exact (htail v hvs).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (I.maxMonomialMagnitude_pos y).le)

/-- The full dominant-face derivative estimate outside a fixed radial
cylinder, first with the ambient coordinate supremum norm as radius.
The face and its tail are constructed from `ToricInput` in the proof. -/
theorem ToricInput.G_dominant_lowerBound_pi (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 0 < L ∧ ∀ y : LGSpace n,
      L ≤ ‖y.1‖ → c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y) := by
  obtain ⟨c, hc, hderivative⟩ := I.G_lowerBound_of_face_tail
  let S : ℝ := ∑ v ∈ I.vertices, ‖latticeComplex v‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun v _ => norm_nonneg _
  let ε : ℝ := c / (1 + S)
  have hε : 0 < ε := div_pos hc (by linarith)
  obtain ⟨L, hL, hconcentrate⟩ := I.monomial_face_concentration hε
  refine ⟨c, hc, L, hL, ?_⟩
  intro y hy
  obtain ⟨s, hs, hne, hproper, hmax, htail⟩ := hconcentrate y hy
  apply hderivative s hs hne hproper y hmax
  have ht := norm_G_sub_faceMonomialDerivative_le I s hs.1 y hε.le htail
  have hεS : ε * S ≤ c := by
    have hcancel : ε * (1 + S) = c := div_mul_cancel₀ c (by linarith : 1 + S ≠ 0)
    nlinarith
  have hbound : ε * maxMonomialMagnitude I y * S ≤ c * maxMonomialMagnitude I y := by
    have hm := mul_le_mul_of_nonneg_right hεS (I.maxMonomialMagnitude_pos y).le
    nlinarith
  exact ht.trans hbound

/-- A fixed finite-dimensional comparison from the based Euclidean radius
to the coordinate supremum norm; no norm convention is silently changed. -/
theorem euclidean_radius_le_mul_pi_norm (u : RealSpace n) :
    Real.sqrt (realSquaredNorm u) ≤ ((n : ℝ) + 1) * ‖u‖ := by
  have hsq : realSquaredNorm u ≤ (n : ℝ) * ‖u‖ ^ 2 := by
    calc
      realSquaredNorm u ≤ ∑ _j : Fin n, ‖u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hj : |u j| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm u j
        have habs := sq_abs (u j)
        nlinarith [abs_nonneg (u j), norm_nonneg u]
      _ = _ := by simp
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (by positivity) (norm_nonneg _), ?_⟩
  have hn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hm := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖u‖)
  nlinarith

/-- Dominant-face noncancellation for the literal derivative vector of the
original superpotential, with exactly the source's Euclidean radial convention.
This proves the derivative part of `lem:dominant` for each finite input. -/
theorem ToricInput.G_dominant_lowerBound (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 0 < L ∧ ∀ y : LGSpace n,
      L ≤ Real.sqrt (realSquaredNorm y.1) →
        c * maxMonomialMagnitude I y ≤ Real.sqrt (a I y) := by
  obtain ⟨c, hc, L, hL, hbound⟩ := I.G_dominant_lowerBound_pi
  have hscale : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨c, hc, ((n : ℝ) + 1) * L, mul_pos hscale hL, ?_⟩
  intro y hy
  apply hbound y
  exact (mul_le_mul_iff_right₀ hscale).mp
    (by simpa only [mul_comm] using hy.trans (euclidean_radius_le_mul_pi_norm y.1))

/-- On a sufficiently large radial end, the source scalar `a = ḠᵀG` is
strictly positive. This is a direct geometric consumer of the dominant-face
estimate, rather than an assumption in an end-bound predicate. -/
theorem ToricInput.a_pos_on_radial_end (I : ToricInput n) :
    ∃ L : ℝ, 0 < L ∧ ∀ y : LGSpace n,
      L ≤ Real.sqrt (realSquaredNorm y.1) → 0 < a I y := by
  obtain ⟨c, hc, L, hL, hbound⟩ := I.G_dominant_lowerBound
  refine ⟨L, hL, ?_⟩
  intro y hy
  exact Real.sqrt_pos.mp ((mul_pos hc (I.maxMonomialMagnitude_pos y)).trans_le (hbound y hy))

/-- All zeros of the native logarithmic derivative have bounded radial
coordinates. This records the critical-point consequence of `lem:dominant`
without a smooth differential realization assumption. -/
theorem ToricInput.G_zero_radial_bound (I : ToricInput n) :
    ∃ L : ℝ, 0 < L ∧ ∀ y : LGSpace n, G I y = 0 →
      Real.sqrt (realSquaredNorm y.1) < L := by
  obtain ⟨L, hL, ha⟩ := I.a_pos_on_radial_end
  refine ⟨L, hL, ?_⟩
  intro y hG
  by_contra h
  have hapos := ha y (le_of_not_gt h)
  have hazero : a I y = 0 := by simp [a, hG]
  linarith

end FsFltz
