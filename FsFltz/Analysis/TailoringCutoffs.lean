import FsFltz.Analysis.FiniteSupportGrowth
import FsFltz.Analysis.SupportMollification
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The literal all-pairs tailoring cutoffs

Source: `geometric-part-fsf-proof.tex`, `eq:cutoffs`, lines 1051–1065,
and the analytic estimates in `lem:cutoffs`, lines 1072–1083.
The exponent set is the actual finite set `{0} ∪ V`; its affine weights
and cutoffs are constructed explicitly. Simplicial containment of retained
exponents is a subsequent, separate geometric statement. All derivative
bounds below concern derivatives in `u`, with constants independent of `β`.
-/

noncomputable section

namespace FsFltz

open Set Filter
open scoped BigOperators Topology ContDiff

variable {n : ℕ}

/-- Zero is interior to the input polytope and therefore is not a vertex. -/
theorem ToricInput.zero_not_mem_vertices (I : ToricInput n) : (0 : Lattice n) ∉ I.vertices := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one I.positive_rank
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  intro hz
  have he : (0 : RealSpace n) ∈ (latticePolytope I.vertices).extremePoints ℝ := by
    rw [← I.vertices_exact]
    exact ⟨0, hz, by ext j; simp [latticeReal]⟩
  exact disjoint_left.mp (disjoint_interior_extremePoints (latticePolytope I.vertices))
    I.zero_interior he

/-- The literal augmented exponent set `A = {0} ∪ V`. -/
def tailoringExponents (I : ToricInput n) : Finset (Lattice n) :=
  insert 0 I.vertices

/-- The source's affine offset: zero for the constant term, one for vertices. -/
def tailoringNu (a : Lattice n) : ℝ := if a = 0 then 0 else 1

@[simp] theorem tailoringNu_zero : tailoringNu (0 : Lattice n) = 0 := by
  simp [tailoringNu]

theorem tailoringNu_vertex (I : ToricInput n) (v : {v : Lattice n // v ∈ I.vertices}) :
    tailoringNu v.val = 1 := by
  have hne : v.val ≠ 0 := fun h => I.zero_not_mem_vertices (h ▸ v.property)
  simp [tailoringNu, hne]

/-- The actual affine log magnitude `ℓ_a(u) = ⟨a,u⟩ - β ν(a)`. -/
def tailoringWeight (β : ℝ) (a : Lattice n) (u : RealSpace n) : ℝ :=
  pairing a u - β * tailoringNu a

@[simp] theorem tailoringWeight_zero (β : ℝ) (u : RealSpace n) :
    tailoringWeight β 0 u = 0 := by
  simp [tailoringWeight, pairing]

theorem tailoringWeight_vertex (I : ToricInput n) (β : ℝ)
    (v : {v : Lattice n // v ∈ I.vertices}) (u : RealSpace n) :
    tailoringWeight β v.val u = pairing v.val u - β := by
  simp [tailoringWeight, tailoringNu_vertex I v]

/-- The affine vertex weight is the actual log magnitude of `e⁻ᵝ zᵛ`. -/
theorem norm_tailoring_monomial (I : ToricInput n) (β : ℝ)
    (v : {v : Lattice n // v ∈ I.vertices}) (y : LGSpace n) :
    ‖monomial (Real.exp (-β) : ℂ) v.val y‖ = Real.exp (tailoringWeight β v.val y.1) := by
  rw [norm_monomial, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), tailoringWeight_vertex I β v, ← Real.exp_add]
  congr 1
  ring

/-- A smooth monotone profile with the prescribed `-2` and `0` tails. -/
def tailoringCutoffProfile (s : ℝ) : ℝ := Real.smoothTransition ((s + 2) / 2)

theorem tailoringCutoffProfile_contDiff : ContDiff ℝ ∞ tailoringCutoffProfile := by
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const 2)

theorem tailoringCutoffProfile_nonneg (s : ℝ) : 0 ≤ tailoringCutoffProfile s :=
  Real.smoothTransition.nonneg _

theorem tailoringCutoffProfile_le_one (s : ℝ) : tailoringCutoffProfile s ≤ 1 :=
  Real.smoothTransition.le_one _

theorem tailoringCutoffProfile_monotone : Monotone tailoringCutoffProfile := by
  intro s t h
  apply Real.smoothTransition.monotone
  linarith

theorem tailoringCutoffProfile_eq_zero_iff (s : ℝ) :
    tailoringCutoffProfile s = 0 ↔ s ≤ -2 := by
  rw [tailoringCutoffProfile, Real.smoothTransition.zero_iff_nonpos]
  constructor <;> intro h <;> linarith

theorem tailoringCutoffProfile_eq_one_iff (s : ℝ) :
    tailoringCutoffProfile s = 1 ↔ 0 ≤ s := by
  rw [tailoringCutoffProfile, Real.smoothTransition.eq_one_iff_one_le]
  constructor <;> intro h <;> linarith

theorem tailoringCutoffProfile_pos_iff (s : ℝ) :
    0 < tailoringCutoffProfile s ↔ -2 < s := by
  rw [lt_iff_le_and_ne]
  simp only [tailoringCutoffProfile_nonneg, true_and, ne_eq,
    eq_comm (a := (0 : ℝ)), tailoringCutoffProfile_eq_zero_iff, not_le]

/-- The all-pairs product of `eq:cutoffs`; no support choices are supplied. -/
def tailoringCutoff (I : ToricInput n) (β : ℝ) (a : Lattice n) (u : RealSpace n) : ℝ :=
  ∏ b ∈ (tailoringExponents I).erase a,
    tailoringCutoffProfile (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)

theorem tailoringCutoff_contDiff (I : ToricInput n) (β : ℝ) (a : Lattice n) :
    ContDiff ℝ ∞ (tailoringCutoff I β a) := by
  unfold tailoringCutoff
  apply contDiff_prod
  intro b _
  apply tailoringCutoffProfile_contDiff.comp
  unfold tailoringWeight pairing
  fun_prop

theorem tailoringCutoff_nonneg (I : ToricInput n) (β : ℝ) (a : Lattice n)
    (u : RealSpace n) : 0 ≤ tailoringCutoff I β a u := by
  exact Finset.prod_nonneg (fun _ _ => tailoringCutoffProfile_nonneg _)

theorem tailoringCutoff_le_one (I : ToricInput n) (β : ℝ) (a : Lattice n)
    (u : RealSpace n) : tailoringCutoff I β a u ≤ 1 := by
  unfold tailoringCutoff
  exact Finset.prod_le_one₀ (fun _ _ => tailoringCutoffProfile_nonneg _)
    (fun _ _ => tailoringCutoffProfile_le_one _)

/-- A term no farther than `√β` below every term is unchanged. -/
theorem tailoringCutoff_eq_one_of_gap (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n)
    (hgap : ∀ b ∈ tailoringExponents I,
      tailoringWeight β b u - Real.sqrt β ≤ tailoringWeight β a u) :
    tailoringCutoff I β a u = 1 := by
  unfold tailoringCutoff
  apply Finset.prod_eq_one
  intro b hb
  apply (tailoringCutoffProfile_eq_one_iff _).mpr
  have h := hgap b (Finset.mem_of_mem_erase hb)
  linarith

/-- Every maximal affine term has cutoff one, as asserted by `lem:cutoffs`. -/
theorem tailoringCutoff_eq_one_of_maximal (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n)
    (hmax : ∀ b ∈ tailoringExponents I, tailoringWeight β b u ≤ tailoringWeight β a u) :
    tailoringCutoff I β a u = 1 := by
  apply tailoringCutoff_eq_one_of_gap
  intro b hb
  exact (sub_le_self _ (Real.sqrt_nonneg β)).trans (hmax b hb)

/-- The largest affine weight is exactly `max(0, h(u) - β)`. -/
def tailoringMaxWeight (I : ToricInput n) (β : ℝ) (u : RealSpace n) : ℝ :=
  max 0 (supportHeight I u - β)

theorem tailoringWeight_le_max (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (ha : a ∈ tailoringExponents I) (u : RealSpace n) :
    tailoringWeight β a u ≤ tailoringMaxWeight I β u := by
  rcases Finset.mem_insert.mp ha with rfl | ha
  · simp [tailoringMaxWeight]
  · rw [tailoringWeight_vertex I β ⟨a, ha⟩]
    exact (sub_le_sub_right (I.pairing_le_supportHeight u ⟨a, ha⟩) β).trans
      (le_max_right _ _)

theorem tailoringMaxWeight_attained (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    ∃ a ∈ tailoringExponents I, tailoringWeight β a u = tailoringMaxWeight I β u := by
  by_cases h : supportHeight I u - β ≤ 0
  · exact ⟨0, Finset.mem_insert_self _ _, by simp [tailoringMaxWeight, max_eq_left h]⟩
  · obtain ⟨v, hv⟩ := I.supportHeight_attained u
    refine ⟨v.val, Finset.mem_insert_of_mem v.property, ?_⟩
    rw [tailoringWeight_vertex I β v, hv]
    exact (max_eq_right (le_of_lt (lt_of_not_ge h))).symm

/-- Retention forces every competing affine term to be within `√β + 2`. -/
theorem tailoringCutoff_retained_gap (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n) (hret : 0 < tailoringCutoff I β a u)
    (b : Lattice n) (hb : b ∈ tailoringExponents I) :
    tailoringWeight β b u - Real.sqrt β - 2 < tailoringWeight β a u := by
  by_cases hba : b = a
  · subst b
    have := Real.sqrt_nonneg β
    linarith
  · have hn := Finset.prod_ne_zero_iff.mp hret.ne'
      b (Finset.mem_erase.mpr ⟨hba, hb⟩)
    have h := (tailoringCutoffProfile_pos_iff _).mp
      (lt_of_le_of_ne (tailoringCutoffProfile_nonneg _) (Ne.symm hn))
    linarith

/-- The exact retention estimate in `lem:cutoffs`. -/
theorem tailoringCutoff_retained_deficit (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n) (hret : 0 < tailoringCutoff I β a u) :
    tailoringMaxWeight I β u - Real.sqrt β - 2 < tailoringWeight β a u := by
  obtain ⟨b, hb, he⟩ := tailoringMaxWeight_attained I β u
  simpa only [he] using tailoringCutoff_retained_gap I β a u hret b hb

/-- At a point where the cutoff is one, its differential vanishes. -/
theorem tailoringCutoff_fderiv_eq_zero_of_eq_one (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n) (he : tailoringCutoff I β a u = 1) :
    fderiv ℝ (tailoringCutoff I β a) u = 0 := by
  apply IsLocalMax.fderiv_eq_zero
  exact Eventually.of_forall (fun y => by rw [he]; exact tailoringCutoff_le_one I β a y)

/-- A changed cutoff, or a nonzero differential, forces a `√β` deficit. -/
theorem tailoringCutoff_changed_deficit (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n)
    (hc : tailoringCutoff I β a u ≠ 1 ∨ fderiv ℝ (tailoringCutoff I β a) u ≠ 0) :
    tailoringWeight β a u < tailoringMaxWeight I β u - Real.sqrt β := by
  have hne : tailoringCutoff I β a u ≠ 1 := by
    rcases hc with hc | hc
    · exact hc
    · exact fun he => hc (tailoringCutoff_fderiv_eq_zero_of_eq_one I β a u he)
  by_contra! hg
  apply hne
  apply tailoringCutoff_eq_one_of_gap
  intro b hb
  exact (sub_le_sub_right (tailoringWeight_le_max I β b hb u) _).trans hg

theorem exp_tailoringMaxWeight (I : ToricInput n) (β : ℝ) (u : RealSpace n) :
    Real.exp (tailoringMaxWeight I β u) = max 1 (Real.exp (supportHeight I u - β)) := by
  unfold tailoringMaxWeight
  by_cases h : supportHeight I u - β ≤ 0
  · rw [max_eq_left h, Real.exp_zero, max_eq_left]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr h
  · have h' : 0 ≤ supportHeight I u - β := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right h', max_eq_right]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr h'

/-- The changed uncut term has magnitude at most `e^(-√β) max(1,M)`. -/
theorem tailoringCutoff_changed_exp_bound (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (u : RealSpace n)
    (hc : tailoringCutoff I β a u ≠ 1 ∨ fderiv ℝ (tailoringCutoff I β a) u ≠ 0) :
    Real.exp (tailoringWeight β a u) ≤
      Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I u - β)) := by
  rw [← exp_tailoringMaxWeight I β u, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := tailoringCutoff_changed_deficit I β a u hc
  linarith

/-- The profile's differential is supported in the fixed transition interval. -/
theorem tailoringCutoffProfile_fderiv_hasCompactSupport :
    HasCompactSupport (fderiv ℝ tailoringCutoffProfile) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 0))
  intro x hx
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have he : tailoringCutoffProfile =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [gt_mem_nhds hx] with y hy
      exact (tailoringCutoffProfile_eq_zero_iff _).mpr hy.le
    rw [he.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (E := ℝ) (0 : ℝ)) x
  · have he : tailoringCutoffProfile =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact (tailoringCutoffProfile_eq_one_iff _).mpr hy.le
    rw [he.fderiv_eq]
    exact congrFun (fderiv_const (𝕜 := ℝ) (E := ℝ) (1 : ℝ)) x

/-- Every fixed order of the scalar profile has a global bound. -/
theorem tailoringCutoffProfile_exists_bound_iteratedFDeriv (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, ‖iteratedFDeriv ℝ m tailoringCutoffProfile s‖ ≤ C := by
  rcases m with _ | m
  · refine ⟨1, zero_le_one, fun s => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs,
      abs_of_nonneg (tailoringCutoffProfile_nonneg s)]
    exact tailoringCutoffProfile_le_one s
  · obtain ⟨C, hC, hb⟩ := tailoringCutoffProfile_fderiv_hasCompactSupport.exists_bound_iteratedFDeriv
        (tailoringCutoffProfile_contDiff.fderiv_right (by simp)) m
    refine ⟨C, hC, fun s => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv]
    exact hb m le_rfl s

private def tailoringProfileDerivativeBound (m : ℕ) : ℝ :=
  (tailoringCutoffProfile_exists_bound_iteratedFDeriv m).choose

private theorem tailoringProfileDerivativeBound_nonneg (m : ℕ) :
    0 ≤ tailoringProfileDerivativeBound m :=
  (tailoringCutoffProfile_exists_bound_iteratedFDeriv m).choose_spec.1

private theorem tailoringProfileDerivativeBound_le (m : ℕ) (s : ℝ) :
    ‖iteratedFDeriv ℝ m tailoringCutoffProfile s‖ ≤ tailoringProfileDerivativeBound m :=
  (tailoringCutoffProfile_exists_bound_iteratedFDeriv m).choose_spec.2 s

private theorem tailoringCutoffFactor_derivative_bound (β : ℝ) (a b : Lattice n)
    (m : ℕ) (u : RealSpace n) :
    ‖iteratedFDeriv ℝ m (fun u : RealSpace n =>
      tailoringCutoffProfile (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)) u‖ ≤
      tailoringProfileDerivativeBound m * ‖pairingCLM a - pairingCLM b‖ ^ m := by
  let L : RealSpace n →L[ℝ] ℝ := pairingCLM a - pairingCLM b
  let c := -β * tailoringNu a + β * tailoringNu b + Real.sqrt β
  let f : ℝ → ℝ := fun s => tailoringCutoffProfile (s + c)
  have hf : ContDiff ℝ ∞ f :=
    tailoringCutoffProfile_contDiff.comp (contDiff_id.add contDiff_const)
  have he : (fun u : RealSpace n => tailoringCutoffProfile
      (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)) = f ∘ L := by
    ext y
    change tailoringCutoffProfile _ = tailoringCutoffProfile _
    congr 1
    simp only [tailoringWeight, L, sub_apply, pairingCLM_apply, c]
    ring
  rw [he, L.iteratedFDeriv_comp_right hf u (by simp)]
  refine ((iteratedFDeriv ℝ m f (L u)).norm_compContinuousLinearMap_le (fun _ => L)).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg L) m)
  simpa only [f, iteratedFDeriv_comp_add_right] using
    tailoringProfileDerivativeBound_le m (L u + c)

/-- Every fixed-order cutoff derivative is bounded independently of `u` and `β`.
The bound depends only on the finite exponent set, the exponent, and the order. -/
theorem tailoringCutoff_exists_bound_iteratedFDeriv (I : ToricInput n)
    (a : Lattice n) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (u : RealSpace n),
      ‖iteratedFDeriv ℝ m (tailoringCutoff I β a) u‖ ≤ C := by
  let S := (tailoringExponents I).erase a
  let C := ∑ p ∈ S.sym m, ((p : Multiset (Lattice n)).countPerms : ℝ) *
    ∏ b ∈ S, tailoringProfileDerivativeBound ((p : Multiset (Lattice n)).count b) *
      ‖pairingCLM a - pairingCLM b‖ ^ ((p : Multiset (Lattice n)).count b)
  refine ⟨C, ?_, fun β u => ?_⟩
  · exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) <|
      Finset.prod_nonneg (fun _ _ => mul_nonneg (tailoringProfileDerivativeBound_nonneg _)
        (pow_nonneg (norm_nonneg _) _)))
  · have hf (b : Lattice n) : ContDiff ℝ ∞ (fun u : RealSpace n =>
        tailoringCutoffProfile (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)) := by
      apply tailoringCutoffProfile_contDiff.comp
      unfold tailoringWeight pairing
      fun_prop
    refine (norm_iteratedFDeriv_prod_le (fun b _ => hf b) (by simp)).trans ?_
    apply Finset.sum_le_sum
    intro p hp
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro b hb
    exact tailoringCutoffFactor_derivative_bound β a b _ u

/-- The finite family admits a single bound at every prescribed derivative order. -/
theorem tailoringCutoffs_exists_uniform_bound_iteratedFDeriv (I : ToricInput n) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (a : Lattice n), a ∈ tailoringExponents I →
      ∀ u : RealSpace n, ‖iteratedFDeriv ℝ m (tailoringCutoff I β a) u‖ ≤ C := by
  choose C hC hb using fun a : Lattice n => tailoringCutoff_exists_bound_iteratedFDeriv I a m
  refine ⟨∑ a ∈ tailoringExponents I, C a,
    Finset.sum_nonneg (fun a _ => hC a), fun β a ha u => ?_⟩
  exact (hb a β u).trans (Finset.single_le_sum (fun b _ => hC b) ha)

/-- Smoothness makes the profile flat, including at the beginning of its one tail. -/
theorem tailoringCutoffProfile_iteratedFDeriv_eq_zero_of_nonneg (m : ℕ) (hm : m ≠ 0)
    (s : ℝ) (hs : 0 ≤ s) : iteratedFDeriv ℝ m tailoringCutoffProfile s = 0 := by
  have he : EqOn (iteratedFDeriv ℝ m tailoringCutoffProfile) (fun _ => 0) (Ioi 0) := by
    intro x hx
    have hlocal : tailoringCutoffProfile =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact (tailoringCutoffProfile_eq_one_iff _).mpr hy.le
    simpa only [iteratedFDeriv_const_of_ne hm, Pi.zero_apply] using
      (hlocal.iteratedFDeriv ℝ m).eq_of_nhds
  have hc := he.closure
    (tailoringCutoffProfile_contDiff.continuous_iteratedFDeriv (by simp)) continuous_const
  exact hc (by rwa [closure_Ioi])

private theorem tailoringCutoffFactor_iteratedFDeriv_eq_zero_of_nonneg
    (β : ℝ) (a b : Lattice n) (m : ℕ) (hm : m ≠ 0) (u : RealSpace n)
    (hs : 0 ≤ tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β) :
    iteratedFDeriv ℝ m (fun u : RealSpace n => tailoringCutoffProfile
      (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)) u = 0 := by
  let L : RealSpace n →L[ℝ] ℝ := pairingCLM a - pairingCLM b
  let c := -β * tailoringNu a + β * tailoringNu b + Real.sqrt β
  let f : ℝ → ℝ := fun s => tailoringCutoffProfile (s + c)
  have hf : ContDiff ℝ ∞ f :=
    tailoringCutoffProfile_contDiff.comp (contDiff_id.add contDiff_const)
  have harg (y : RealSpace n) :
      tailoringWeight β a y - tailoringWeight β b y + Real.sqrt β = L y + c := by
    simp only [tailoringWeight, L, sub_apply, pairingCLM_apply, c]
    ring
  have he : (fun u : RealSpace n => tailoringCutoffProfile
      (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)) = f ∘ L := by
    ext y
    exact congrArg tailoringCutoffProfile (harg y)
  rw [he, L.iteratedFDeriv_comp_right hf u (by simp)]
  have hzero : iteratedFDeriv ℝ m f (L u) = 0 := by
    rw [iteratedFDeriv_comp_add_right]
    exact tailoringCutoffProfile_iteratedFDeriv_eq_zero_of_nonneg m hm _ (harg u ▸ hs)
  rw [hzero]
  ext y
  rfl

/-- Every positive-order derivative vanishes throughout the unchanged gap region. -/
theorem tailoringCutoff_iteratedFDeriv_eq_zero_of_gap (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (m : ℕ) (hm : m ≠ 0) (u : RealSpace n)
    (hgap : ∀ b ∈ tailoringExponents I,
      tailoringWeight β b u - Real.sqrt β ≤ tailoringWeight β a u) :
    iteratedFDeriv ℝ m (tailoringCutoff I β a) u = 0 := by
  rcases m with _ | m
  · exact (hm rfl).elim
  let S := (tailoringExponents I).erase a
  let f : Lattice n → RealSpace n → ℝ := fun b u => tailoringCutoffProfile
    (tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β)
  have hf (b : Lattice n) : ContDiff ℝ ∞ (f b) := by
    apply tailoringCutoffProfile_contDiff.comp
    unfold tailoringWeight pairing
    fun_prop
  have hbound := norm_iteratedFDeriv_prod_le (u := S) (fun b _ => hf b)
    (x := u) (n := m + 1) (by simp)
  have hz : (∑ p ∈ S.sym (m + 1), ((p : Multiset (Lattice n)).countPerms : ℝ) *
      ∏ b ∈ S, ‖iteratedFDeriv ℝ ((p : Multiset (Lattice n)).count b) (f b) u‖) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨b, hb⟩ := p.exists_mem
    have hbS : b ∈ S := Finset.mem_sym_iff.mp hp b hb
    have hcount : (p : Multiset (Lattice n)).count b ≠ 0 :=
      (Multiset.count_pos.mpr (Sym.mem_coe.mpr hb)).ne'
    have hnonneg : 0 ≤ tailoringWeight β a u - tailoringWeight β b u + Real.sqrt β := by
      have := hgap b (Finset.mem_of_mem_erase hbS)
      linarith
    have hprod : (∏ j ∈ S, ‖iteratedFDeriv ℝ ((p : Multiset (Lattice n)).count j)
        (f j) u‖) = 0 := by
      apply Finset.prod_eq_zero hbS
      exact norm_eq_zero.mpr
        (tailoringCutoffFactor_iteratedFDeriv_eq_zero_of_nonneg β a b _ hcount u hnonneg)
    rw [hprod, mul_zero]
  apply norm_le_zero_iff.mp
  exact hz ▸ hbound

/-- The exponential smallness estimate applies to every nonzero positive-order derivative. -/
theorem tailoringCutoff_derivative_exp_bound (I : ToricInput n) (β : ℝ)
    (a : Lattice n) (m : ℕ) (hm : m ≠ 0) (u : RealSpace n)
    (hd : iteratedFDeriv ℝ m (tailoringCutoff I β a) u ≠ 0) :
    Real.exp (tailoringWeight β a u) ≤
      Real.exp (-Real.sqrt β) * max 1 (Real.exp (supportHeight I u - β)) := by
  have hg : tailoringWeight β a u < tailoringMaxWeight I β u - Real.sqrt β := by
    by_contra! hg
    apply hd
    apply tailoringCutoff_iteratedFDeriv_eq_zero_of_gap I β a m hm u
    intro b hb
    exact (sub_le_sub_right (tailoringWeight_le_max I β b hb u) _).trans hg
  rw [← exp_tailoringMaxWeight I β u, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end FsFltz
