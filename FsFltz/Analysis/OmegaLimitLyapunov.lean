import Mathlib.Dynamics.OmegaLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Lyapunov derivatives on forward omega-limit sets

Source: `geometric-part-fsf-proof.tex`, `thm:core`, lines 1734–1743.
The scalar derivative is explicit; the geometric application supplies it
from the actual intrinsic Liouville field and its strict Lyapunov theorem.
-/

namespace FsFltz

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- Monotonicity and continuity determine the value at every forward limit
point as the supremum of the values along the same actual orbit. -/
theorem omegaLimit_lyapunov_value (φ : Flow ℝ X) {V : X → ℝ}
    (hV : Continuous V) {x : X}
    (hmono : Monotone (fun t => V (φ t x)))
    (hbdd : BddAbove (range (fun t => V (φ t x))))
    {y : X} (hy : y ∈ omegaLimit atTop φ {x}) :
    V y = ⨆ t : ℝ, V (φ t x) := by
  apply le_antisymm
  · have ht := omegaLimit_subset_closure_image2 atTop φ {x} (Ici_mem_atTop (0 : ℝ)) hy
    apply closure_minimal (t := {z | V z ≤ ⨆ t : ℝ, V (φ t x)}) ?_
      (isClosed_le hV continuous_const) ht
    rintro z ⟨t, _, w, hw, rfl⟩
    have : w = x := mem_singleton_iff.mp hw
    subst w
    exact le_ciSup hbdd t
  · apply ciSup_le
    intro s
    have ht := omegaLimit_subset_closure_image2 atTop φ {x} (Ici_mem_atTop s) hy
    apply closure_minimal (t := {z | V (φ s x) ≤ V z}) ?_
      (isClosed_le continuous_const hV) ht
    rintro z ⟨t, ht, w, hw, rfl⟩
    have : w = x := mem_singleton_iff.mp hw
    subst w
    exact hmono ht

/-- Invariance upgrades the constant limit-set value to vanishing of the
actual derivative along the flow, with no isolation assumption on zeros. -/
theorem omegaLimit_lyapunov_derivative_zero (φ : Flow ℝ X) {V d : X → ℝ}
    (hV : Continuous V) {x : X}
    (hmono : Monotone (fun t => V (φ t x)))
    (hbdd : BddAbove (range (fun t => V (φ t x))))
    (hderiv : ∀ y, HasDerivAt (fun t => V (φ t y)) (d y) 0) :
    omegaLimit atTop φ {x} ⊆ {y | d y = 0} := by
  intro y hy
  have hinv := φ.isInvariant_omegaLimit atTop {x}
    (fun t => tendsto_atTop_add_const_left atTop t tendsto_id)
  have heq : (fun t => V (φ t y)) = fun _ => ⨆ t : ℝ, V (φ t x) := by
    funext t
    exact omegaLimit_lyapunov_value φ hV hmono hbdd (hinv t hy)
  have hd := hderiv y
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const 0 _)

/-- A relatively compact forward orbit has a nonempty omega-limit set on
which its nonnegative Lyapunov derivative vanishes. -/
theorem omegaLimit_nonempty_subset_lyapunov_zero [T2Space X]
    (φ : Flow ℝ X) {V d : X → ℝ} (hV : Continuous V)
    (hderiv : ∀ y t, HasDerivAt (fun s => V (φ s y)) (d (φ t y)) t)
    (hnonneg : ∀ y, 0 ≤ d y) {x : X}
    (hcompact : IsCompact (closure (φ.forwardOrbit x))) :
    (omegaLimit atTop φ {x}).Nonempty ∧
      omegaLimit atTop φ {x} ⊆ {y | d y = 0} := by
  have hmono : Monotone (fun t => V (φ t x)) :=
    monotone_of_hasDerivAt_nonneg (hderiv x) (fun t => hnonneg (φ t x))
  have hmem (t : ℝ) (ht : 0 ≤ t) : φ t x ∈ closure (φ.forwardOrbit x) := by
    apply subset_closure
    rw [φ.forwardOrbit_eq_range_nonneg]
    exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨b, hb⟩ := hcompact.bddAbove_image hV.continuousOn
  have hbdd : BddAbove (range (fun t => V (φ t x))) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · exact hb (mem_image_of_mem V (hmem t ht))
    · exact (hmono (le_of_not_ge ht)).trans
        (hb (mem_image_of_mem V (hmem 0 le_rfl)))
  constructor
  · apply nonempty_omegaLimit_of_isCompact_absorbing atTop φ {x} hcompact
      ?_ (singleton_nonempty x)
    refine ⟨Ici (0 : ℝ), Ici_mem_atTop 0, ?_⟩
    apply closure_minimal ?_ isClosed_closure
    rintro _ ⟨t, ht, y, hy, rfl⟩
    have : y = x := mem_singleton_iff.mp hy
    subst y
    exact hmem t ht
  · apply omegaLimit_lyapunov_derivative_zero φ hV hmono hbdd
    intro y
    simpa only [φ.map_zero, id_eq] using hderiv y 0

end FsFltz
