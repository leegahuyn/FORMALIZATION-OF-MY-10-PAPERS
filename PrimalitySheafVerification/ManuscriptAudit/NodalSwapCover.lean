import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-!
# The two-copy algebra with swapped branch gluing

Each factor is one polynomial normalization. At the two conductor
branches the scalar values are matched across the two copies.
-/

namespace ManuscriptAudit.NodalSwapCover

open NodalConductor Polynomial

universe u

variable (K : Type u) [Field K]

/-- Pairs of polynomials whose branch values are identified crosswise. -/
def crossedPairs : Subalgebra (coordinates K) (K[X] × K[X]) where
  carrier := {f | f.1.eval 1 = f.2.eval (-1) ∧ f.1.eval (-1) = f.2.eval 1}
  zero_mem' := by
    change (0 : K[X]).eval 1 = (0 : K[X]).eval (-1) ∧
      (0 : K[X]).eval (-1) = (0 : K[X]).eval 1
    simp
  one_mem' := by
    change (1 : K[X]).eval 1 = (1 : K[X]).eval (-1) ∧
      (1 : K[X]).eval (-1) = (1 : K[X]).eval 1
    simp
  add_mem' := by
    rintro f g ⟨hf₁, hf₂⟩ ⟨hg₁, hg₂⟩
    change (f.1 + g.1).eval 1 = (f.2 + g.2).eval (-1) ∧
      (f.1 + g.1).eval (-1) = (f.2 + g.2).eval 1
    exact ⟨by simp only [eval_add, hf₁, hg₁], by simp only [eval_add, hf₂, hg₂]⟩
  mul_mem' := by
    rintro f g ⟨hf₁, hf₂⟩ ⟨hg₁, hg₂⟩
    change (f.1 * g.1).eval 1 = (f.2 * g.2).eval (-1) ∧
      (f.1 * g.1).eval (-1) = (f.2 * g.2).eval 1
    exact ⟨by simp only [eval_mul, hf₁, hg₁], by simp only [eval_mul, hf₂, hg₂]⟩
  algebraMap_mem' := by
    intro f
    have h := (mem_equalBranchValues K f.val).mp (coordinates_le_equalBranchValues K f.property)
    exact ⟨h, h.symm⟩

abbrev Cover : Type u := ↥(crossedPairs K)

theorem condition (z : Cover K) :
    z.val.1.eval 1 = z.val.2.eval (-1) ∧ z.val.1.eval (-1) = z.val.2.eval 1 :=
  z.property

theorem algebraMap_pair (a : coordinates K) :
    (algebraMap (coordinates K) (Cover K) a).val = (a.val, a.val) :=
  rfl

/-- Swapping the two normalization copies gives an involution over the node. -/
def swap : Cover K ≃ₐ[coordinates K] Cover K where
  toFun z := ⟨(z.val.2, z.val.1), (condition K z).2.symm, (condition K z).1.symm⟩
  invFun z := ⟨(z.val.2, z.val.1), (condition K z).2.symm, (condition K z).1.symm⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

theorem swap_twice (z : Cover K) : swap K (swap K z) = z :=
  Subtype.ext rfl

theorem swap_nontrivial : ∃ z : Cover K, swap K z ≠ z := by
  have hx : x K ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    simpa [x] using hc
  let z : Cover K := ⟨(x K, 0), by
    change (x K).eval 1 = (0 : K[X]).eval (-1) ∧
      (x K).eval (-1) = (0 : K[X]).eval 1
    simp [x]⟩
  refine ⟨z, ?_⟩
  intro h
  have hz : (0 : K[X]) = x K := congrArg (fun w : Cover K => w.val.1) h
  exact hx hz.symm

/-- The fixed elements of the involution are precisely the actual nodal ring. -/
theorem swap_fixed_iff_from_node (h2 : (2 : K) ≠ 0) (z : Cover K) :
    swap K z = z ↔ ∃ a : coordinates K, algebraMap (coordinates K) (Cover K) a = z := by
  constructor
  · intro h
    have hf : z.val.2 = z.val.1 := congrArg (fun w : Cover K => w.val.1) h
    have hz : z.val.1 ∈ coordinates K := by
      rw [coordinates_eq_equalBranchValues K h2, mem_equalBranchValues]
      exact (condition K z).1.trans (congrArg (fun f : K[X] => f.eval (-1)) hf)
    refine ⟨⟨z.val.1, hz⟩, Subtype.ext ?_⟩
    exact Prod.ext rfl hf.symm
  · rintro ⟨a, rfl⟩
    exact Subtype.ext rfl

private theorem polynomial_idempotent (f : K[X]) (h : f * f = f) :
    f = 0 ∨ f = 1 := by
  have hz : f * (f - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  exact (mul_eq_zero.mp hz).imp id sub_eq_zero.mp

/-- The crossed algebra has no nontrivial idempotent. -/
theorem idempotent_eq_zero_or_one (z : Cover K) (h : z * z = z) :
    z = 0 ∨ z = 1 := by
  have h₁ : z.val.1 * z.val.1 = z.val.1 := congrArg (fun w : Cover K => w.val.1) h
  have h₂ : z.val.2 * z.val.2 = z.val.2 := congrArg (fun w : Cover K => w.val.2) h
  have hb := (condition K z).1
  rcases polynomial_idempotent K z.val.1 h₁ with e₁ | e₁ <;>
    rcases polynomial_idempotent K z.val.2 h₂ with e₂ | e₂
  · exact Or.inl (Subtype.ext (Prod.ext e₁ e₂))
  · have hn : (0 : K) = 1 := by simpa only [e₁, e₂, eval_zero, eval_one] using hb
    exact (zero_ne_one hn).elim
  · have hn : (1 : K) = 0 := by simpa only [e₁, e₂, eval_zero, eval_one] using hb
    exact (one_ne_zero hn).elim
  · exact Or.inr (Subtype.ext (Prod.ext e₁ e₂))

end ManuscriptAudit.NodalSwapCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCover.algebraMap_pair,
        ``ManuscriptAudit.NodalSwapCover.swap_twice,
        ``ManuscriptAudit.NodalSwapCover.swap_nontrivial,
        ``ManuscriptAudit.NodalSwapCover.swap_fixed_iff_from_node,
        ``ManuscriptAudit.NodalSwapCover.idempotent_eq_zero_or_one] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
