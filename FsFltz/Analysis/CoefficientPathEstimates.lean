import FsFltz.Analysis.CoefficientPath
import FsFltz.Analysis.DominantFace

/-!
# Dominant-face estimates uniform in the prescribed coefficient path

Source: `geometric-part-fsf-proof.tex`, `lem:dominant`, lines 697–709,
`lem:margin`, lines 753–757, and the matching-truncation estimates,
lines 1011–1035. Common constants are first constructed for every coefficient
tuple with fixed support and common positive lower and finite upper bounds.
The compact nonvanishing path supplies these bounds and consumes the result.
These statements concern the actual finite monomials and derivative; they do
not assert existence of a geometric deformation or a completion marking.
-/

noncomputable section

namespace FsFltz

open scoped BigOperators Topology

variable {n : ℕ}

/-- A common coefficient lower bound controls the actual maximum at support
height. This statement holds on the entire quotient ambient. -/
theorem ToricInput.coeff_lowerBound_mul_exp_supportHeight_le
    (I : ToricInput n) {A : ℝ}
    (hlower : ∀ v : {v : Lattice n // v ∈ I.vertices}, A ≤ ‖I.coeff v‖)
    (y : LGSpace n) :
    A * Real.exp (supportHeight I y.1) ≤ maxMonomialMagnitude I y := by
  obtain ⟨v, hv⟩ := I.supportHeight_attained y.1
  calc
    A * Real.exp (supportHeight I y.1) ≤
        ‖I.coeff v‖ * Real.exp (supportHeight I y.1) :=
      mul_le_mul_of_nonneg_right (hlower v) (Real.exp_pos _).le
    _ = ‖monomial (I.coeff v) v.val y‖ := by rw [norm_monomial, hv]
    _ ≤ maxMonomialMagnitude I y := I.norm_monomial_le_maxMonomialMagnitude y v

/-- The common coefficient ratio bounds every monomial's exponential tail.
No constant is chosen separately for individual coefficient tuples. -/
theorem ToricInput.monomial_deficit_bound_of_coeff_bounds
    (I : ToricInput n) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hcoeff : ∀ v : {v : Lattice n // v ∈ I.vertices},
      A ≤ ‖I.coeff v‖ ∧ ‖I.coeff v‖ ≤ B)
    (y : LGSpace n) (v : {v : Lattice n // v ∈ I.vertices}) :
    ‖monomial (I.coeff v) v.val y‖ ≤
      B / A * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
        maxMonomialMagnitude I y := by
  have hM := I.coeff_lowerBound_mul_exp_supportHeight_le (fun w => (hcoeff w).1) y
  have hexp : Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
      Real.exp (supportHeight I y.1) = Real.exp (pairing v.val y.1) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖monomial (I.coeff v) v.val y‖ = ‖I.coeff v‖ * Real.exp (pairing v.val y.1) :=
      norm_monomial _ _ _
    _ ≤ B * Real.exp (pairing v.val y.1) :=
      mul_le_mul_of_nonneg_right (hcoeff v).2 (Real.exp_pos _).le
    _ = B / A * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
        (A * Real.exp (supportHeight I y.1)) := by
      rw [mul_assoc, mul_left_comm _ A, ← mul_assoc,
        div_mul_cancel₀ _ (ne_of_gt hA), hexp]
    _ ≤ B / A * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) *
        maxMonomialMagnitude I y :=
      mul_le_mul_of_nonneg_left hM (by positivity)

/-- Any positive relative tolerance has one finite deficit cutoff uniform
over every coefficient tuple in the common annulus. -/
theorem monomial_tail_cutoff_of_coeff_bounds {A B ε : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ I : ToricInput n,
      (∀ v : {v : Lattice n // v ∈ I.vertices},
        A ≤ ‖I.coeff v‖ ∧ ‖I.coeff v‖ ≤ B) →
      ∀ y : LGSpace n, ∀ v : {v : Lattice n // v ∈ I.vertices},
        D ≤ supportHeight I y.1 - pairing v.val y.1 →
          ‖monomial (I.coeff v) v.val y‖ ≤ ε * maxMonomialMagnitude I y := by
  let C := B / A
  have hC : 0 < C := div_pos hB hA
  refine ⟨max 1 (Real.log (C / ε)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro I hcoeff y v hD
  have hgap : Real.log (C / ε) ≤ supportHeight I y.1 - pairing v.val y.1 :=
    (le_max_right _ _).trans hD
  have hexp : C * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) ≤ ε := by
    calc
      C * Real.exp (-(supportHeight I y.1 - pairing v.val y.1)) ≤
          C * Real.exp (-Real.log (C / ε)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hgap)) hC.le
      _ = ε := by
        rw [Real.exp_neg, Real.exp_log (div_pos hC hε)]
        field_simp
  exact (I.monomial_deficit_bound_of_coeff_bounds hA hB hcoeff y v).trans
    (mul_le_mul_of_nonneg_right hexp (I.maxMonomialMagnitude_pos y).le)

/-- Uniform face concentration for all coefficients in a common annulus.
The radius depends on the original support geometry and on the common
coefficient ratio, uniformly over the coefficient tuple and quotient torus. -/
theorem ToricInput.uniform_monomial_face_concentration_of_coeff_bounds
    (I : ToricInput n) {A B ε : ℝ} (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ J : ToricInput n, J.vertices = I.vertices →
      (∀ v : {v : Lattice n // v ∈ J.vertices},
        A ≤ ‖J.coeff v‖ ∧ ‖J.coeff v‖ ≤ B) →
      ∀ y : LGSpace n, L ≤ ‖y.1‖ →
        ∃ s, ∃ hs : IsPolytopeFace J.vertices s,
          s.Nonempty ∧ s ≠ J.vertices ∧
          (∃ v : {v : Lattice n // v ∈ s},
            ‖monomial (J.coeff ⟨v.val, hs.1 v.property⟩) v.val y‖ =
              maxMonomialMagnitude J y) ∧
          (∀ v : {v : Lattice n // v ∈ J.vertices}, v.val ∉ s →
            ‖monomial (J.coeff v) v.val y‖ ≤ ε * maxMonomialMagnitude J y) := by
  classical
  let q : ℝ := min ε (1 / 2)
  have hq : 0 < q := lt_min hε (by norm_num)
  obtain ⟨D, hD, hcutoff⟩ := monomial_tail_cutoff_of_coeff_bounds (n := n) hA hB hq
  obtain ⟨δ, hδ, hface⟩ := I.uniform_pairingGap_face
  let L : ℝ := 1 + D / δ
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro J hvertices hcoeff y hy
  have hunorm : 0 < ‖y.1‖ := hL.trans_le hy
  have hu : y.1 ≠ 0 := norm_pos_iff.mp hunorm
  have hheight : supportHeight J y.1 = supportHeight I y.1 := by
    exact congrArg (fun s : Finset (Lattice n) =>
      sSup (Set.range (fun v : {v : Lattice n // v ∈ s} => pairing v.val y.1))) hvertices
  have hgapnorm : D ≤ δ * ‖y.1‖ := by
    have hdiv : D / δ ≤ ‖y.1‖ := by dsimp [L] at hy; linarith
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hdiv
  let t := J.vertices.filter (fun v => supportHeight J y.1 - pairing v y.1 ≤ D)
  have htV : t ⊆ I.vertices := by
    rw [← hvertices]
    exact Finset.filter_subset _ _
  have htgap : ∀ v ∈ t, supportHeight I y.1 - pairing v y.1 ≤ δ * ‖y.1‖ := by
    intro v hv
    rw [← hheight]
    exact (Finset.mem_filter.mp hv).2.trans hgapnorm
  obtain ⟨s, hsI, hsne, hsproperI, hts⟩ := hface y.1 hu t htV htgap
  have hs : IsPolytopeFace J.vertices s := by simpa only [hvertices] using hsI
  have hsproper : s ≠ J.vertices := by simpa only [hvertices] using hsproperI
  have htail : ∀ v : {v : Lattice n // v ∈ J.vertices}, v.val ∉ s →
      ‖monomial (J.coeff v) v.val y‖ ≤ q * maxMonomialMagnitude J y := by
    intro v hvs
    have hvt : v.val ∉ t := fun hv => hvs (hts hv)
    have hdef : D < supportHeight J y.1 - pairing v.val y.1 := by
      apply lt_of_not_ge
      intro he
      exact hvt (Finset.mem_filter.mpr ⟨v.property, he⟩)
    exact hcutoff J hcoeff y v hdef.le
  refine ⟨s, hs, hsne, hsproper, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := J.maxMonomialMagnitude_attained y
    have hvs : v.val ∈ s := by
      by_contra hvs
      have ht := htail v hvs
      rw [hv] at ht
      have hqM := mul_le_mul_of_nonneg_right (min_le_right ε (1 / 2))
        (J.maxMonomialMagnitude_pos y).le
      change q * maxMonomialMagnitude J y ≤ _ at hqM
      linarith [J.maxMonomialMagnitude_pos y]
    exact ⟨⟨v.val, hvs⟩, hv⟩
  · intro v hvs
    exact (htail v hvs).trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (J.maxMonomialMagnitude_pos y).le)

/-- One Euclidean derivative-dominance constant and one end radius work
for every coefficient tuple in the common annulus with the original support.
Proper-face independence is supplied by the original lattice facet bases. -/
theorem ToricInput.uniform_G_dominant_lowerBound_of_coeff_bounds
    (I : ToricInput n) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 0 < L ∧
      ∀ J : ToricInput n, J.vertices = I.vertices →
        (∀ v : {v : Lattice n // v ∈ J.vertices},
          A ≤ ‖J.coeff v‖ ∧ ‖J.coeff v‖ ≤ B) →
        ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
          c * maxMonomialMagnitude J y ≤ Real.sqrt (a J y) := by
  obtain ⟨d, hd, hface⟩ := I.uniform_complex_face_lowerBound
  let c : ℝ := d / 2
  have hc : 0 < c := half_pos hd
  let S : ℝ := ∑ v ∈ I.vertices, ‖latticeComplex v‖
  have hS : 0 ≤ S := Finset.sum_nonneg fun v _ => norm_nonneg _
  let ε : ℝ := c / (1 + S)
  have hε : 0 < ε := div_pos hc (by linarith)
  obtain ⟨L, hL, hconcentrate⟩ :=
    I.uniform_monomial_face_concentration_of_coeff_bounds hA hB hε
  have hscale : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨c, hc, ((n : ℝ) + 1) * L, mul_pos hscale hL, ?_⟩
  intro J hvertices hcoeff y hy
  have hyPi : L ≤ ‖y.1‖ := (mul_le_mul_iff_right₀ hscale).mp
    (by simpa only [mul_comm] using hy.trans (euclidean_radius_le_mul_pi_norm y.1))
  obtain ⟨s, hs, hne, hproper, hmax, htail⟩ :=
    hconcentrate J hvertices hcoeff y hyPi
  have hsI : IsPolytopeFace I.vertices s := by simpa only [hvertices] using hs
  have hproperI : s ≠ I.vertices := by simpa only [hvertices] using hproper
  let γ : {v : Lattice n // v ∈ s} → ℂ :=
    fun v => monomial (J.coeff ⟨v.val, hs.1 v.property⟩) v.val y
  obtain ⟨v, hv⟩ := hmax
  have hcoeffMax : maxMonomialMagnitude J y ≤ ‖γ‖ := by
    rw [← hv]
    exact norm_le_pi_norm γ v
  have hlower : d * maxMonomialMagnitude J y ≤
      ‖faceMonomialDerivative J s hs.1 y‖ :=
    (mul_le_mul_of_nonneg_left hcoeffMax hd.le).trans
      (hface s hsI hne hproperI γ)
  have ht := norm_G_sub_faceMonomialDerivative_le J s hs.1 y hε.le htail
  have hsum : (∑ v ∈ J.vertices, ‖latticeComplex v‖) = S := by
    simp only [hvertices, S]
  rw [hsum] at ht
  have hεS : ε * S ≤ c := by
    have hcancel : ε * (1 + S) = c := div_mul_cancel₀ c (by linarith : 1 + S ≠ 0)
    nlinarith
  have htailBound : ‖G J y - faceMonomialDerivative J s hs.1 y‖ ≤
      c * maxMonomialMagnitude J y := by
    have hm := mul_le_mul_of_nonneg_right hεS (J.maxMonomialMagnitude_pos y).le
    exact ht.trans (by nlinarith)
  have htriangle := norm_le_insert (G J y) (faceMonomialDerivative J s hs.1 y)
  have hG : c * maxMonomialMagnitude J y ≤ ‖G J y‖ := by
    dsimp [c] at *
    linarith
  exact hG.trans (norm_G_le_sqrt_a J y)

/-- The actual prescribed nonvanishing coefficient path consumes compactness
and the uniform annulus estimate. Both constants are fixed before the
parameter, radius, or ambient point is supplied. -/
theorem ToricInput.coefficientPath_G_dominant_lowerBound (I : ToricInput n) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n, L ≤ Real.sqrt (realSquaredNorm y.1) →
        c * maxMonomialMagnitude (I.alongCoefficientPath t) y ≤
          Real.sqrt (a (I.alongCoefficientPath t) y) := by
  obtain ⟨A, B, hA, hB, hcoeff⟩ := I.coefficientPath_uniform_norm_bounds
  obtain ⟨c, hc, L, hL, hbound⟩ := I.uniform_G_dominant_lowerBound_of_coeff_bounds hA hB
  exact ⟨c, hc, L, hL, fun t ht =>
    hbound (I.alongCoefficientPath t) rfl (hcoeff t ht)⟩

/-- The common coefficient bounds give the source's bounded logarithmic
derivative error with the explicit coefficient-mass ratio `card(V) B / A`. -/
theorem ToricInput.b0_sub_supportHeight_mul_W_bound_of_coeff_bounds
    (I : ToricInput n) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hcoeff : ∀ v : {v : Lattice n // v ∈ I.vertices},
      A ≤ ‖I.coeff v‖ ∧ ‖I.coeff v‖ ≤ B) (y : LGSpace n) :
    ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤
      (I.vertices.card : ℝ) * B / A * maxMonomialMagnitude I y := by
  have hmass : (∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖) ≤
      (I.vertices.card : ℝ) * B := by
    calc
      (∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖) ≤ ∑ _v :
          {v : Lattice n // v ∈ I.vertices}, B := Finset.sum_le_sum (fun v _ => (hcoeff v).2)
      _ = _ := by simp
  have hM := I.coeff_lowerBound_mul_exp_supportHeight_le (fun v => (hcoeff v).1) y
  calc
    ‖b0 I y - (supportHeight I y.1 : ℂ) * W I y‖ ≤
        (∑ v : {v : Lattice n // v ∈ I.vertices}, ‖I.coeff v‖) *
          Real.exp (supportHeight I y.1) := I.b0_sub_supportHeight_mul_W_le y
    _ ≤ (I.vertices.card : ℝ) * B * Real.exp (supportHeight I y.1) :=
      mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le
    _ = (I.vertices.card : ℝ) * B / A *
        (A * Real.exp (supportHeight I y.1)) := by field_simp
    _ ≤ (I.vertices.card : ℝ) * B / A * maxMonomialMagnitude I y :=
      mul_le_mul_of_nonneg_left hM (by positivity)

/-- Exponential growth is uniform along the actual coefficient path, on
the whole ambient, using its common positive coefficient minimum. -/
theorem ToricInput.coefficientPath_maxMonomialMagnitude_exponential_lowerBound
    (I : ToricInput n) :
    ∃ A : ℝ, 0 < A ∧ ∃ d : ℝ, 0 < d ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ y : LGSpace n,
        A * Real.exp (d * Real.sqrt (realSquaredNorm y.1)) ≤
          maxMonomialMagnitude (I.alongCoefficientPath t) y := by
  obtain ⟨A, B, hA, hB, hcoeff⟩ := I.coefficientPath_uniform_norm_bounds
  obtain ⟨d, hd, hsupport⟩ := I.exists_pairing_ge_euclidean
  refine ⟨A, hA, d, hd, ?_⟩
  intro t ht y
  obtain ⟨v, hv, hpair⟩ := hsupport y.1
  let w : {v : Lattice n // v ∈ I.vertices} := ⟨v, hv⟩
  calc
    A * Real.exp (d * Real.sqrt (realSquaredNorm y.1)) ≤
        ‖coefficientPath I t w‖ * Real.exp (pairing v y.1) :=
      mul_le_mul (hcoeff t ht w).1 (Real.exp_le_exp.mpr hpair)
        (Real.exp_pos _).le (norm_nonneg _)
    _ = ‖monomial ((I.alongCoefficientPath t).coeff w) w.val y‖ :=
      (norm_monomial _ _ _).symm
    _ ≤ maxMonomialMagnitude (I.alongCoefficientPath t) y :=
      (I.alongCoefficientPath t).norm_monomial_le_maxMonomialMagnitude y w

/-- The error constant in `lem:margin` is fixed uniformly before any
coefficient-path member or ambient point is supplied. -/
theorem ToricInput.coefficientPath_b0_sub_supportHeight_mul_W_bound (I : ToricInput n) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      ‖b0 (I.alongCoefficientPath t) y - (supportHeight I y.1 : ℂ) *
        W (I.alongCoefficientPath t) y‖ ≤
          C * maxMonomialMagnitude (I.alongCoefficientPath t) y := by
  obtain ⟨A, B, hA, hB, hcoeff⟩ := I.coefficientPath_uniform_norm_bounds
  have hcard : 0 < (I.vertices.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr I.vertices_nonempty
  refine ⟨(I.vertices.card : ℝ) * B / A, div_pos (mul_pos hcard hB) hA, ?_⟩
  intro t ht y
  exact (I.alongCoefficientPath t).b0_sub_supportHeight_mul_W_bound_of_coeff_bounds
    hA hB (hcoeff t ht) y

/-- The actual logarithmic derivative is nonzero outside a common compact
radial cylinder for every member of the prescribed compact path. -/
theorem ToricInput.coefficientPath_a_pos_on_radial_end (I : ToricInput n) :
    ∃ L : ℝ, 0 < L ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y : LGSpace n,
      L ≤ Real.sqrt (realSquaredNorm y.1) → 0 < a (I.alongCoefficientPath t) y := by
  obtain ⟨c, hc, L, hL, hbound⟩ := I.coefficientPath_G_dominant_lowerBound
  exact ⟨L, hL, fun t ht y hy => Real.sqrt_pos.mp
    ((mul_pos hc ((I.alongCoefficientPath t).maxMonomialMagnitude_pos y)).trans_le
      (hbound t ht y hy))⟩

end FsFltz
