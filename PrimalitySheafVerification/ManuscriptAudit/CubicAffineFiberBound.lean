import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwoPointFiberCard
import PrimalitySheafVerification.ManuscriptAudit.CubicAbscissaFibers
import Mathlib.Algebra.Polynomial.Roots

/-! Native affine points over roots of a nonzero polynomial have cardinal at most twice its degree. -/

namespace ManuscriptAudit.CubicAffineFiberBound

open Polynomial WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicAbscissaFibers

noncomputable section
open scoped Classical

variable {L X : Type*} [Field L] [DecidableEq L] {A : L}

/-- Every injective family of affine points above polynomial roots satisfies the degree bound. -/
theorem card_le_of_root_abscissas (hΔ : (shortCubic (0 : L) A).Δ ≠ 0)
    {f : L[X]} (hf : f ≠ 0) (P : X → (Curve A).Point) (hP : Function.Injective P)
    (hRoot : ∀ i, ∃ (x y : L) (hxy : (Curve A).Nonsingular x y),
      P i = .some x y hxy ∧ f.IsRoot x) :
    Nat.card X ≤ 2 * f.natDegree := by
  let T := f.roots.toFinset
  let a (i : X) : T := by
    refine ⟨(P i).xRep 0, ?_⟩
    obtain ⟨x, y, hxy, he, hx⟩ := hRoot i
    rw [he]
    change x ∈ f.roots.toFinset
    exact Multiset.mem_toFinset.mpr ((mem_roots hf).mpr hx)
  have hFib (i j k : X) (hij : a i = a j) (hik : a i = a k) :
      i = j ∨ i = k ∨ j = k := by
    have eij := congrArg Subtype.val hij
    have eik := congrArg Subtype.val hik
    change (P i).xRep 0 = (P j).xRep 0 at eij
    change (P i).xRep 0 = (P k).xRep 0 at eik
    obtain ⟨x, y, hxy, he, hx⟩ := hRoot i
    obtain ⟨x', y', hxy', he', hx'⟩ := hRoot j
    obtain ⟨x'', y'', hxy'', he'', hx''⟩ := hRoot k
    rw [he, he'] at eij
    rw [he, he''] at eik
    change x = x' at eij
    change x = x'' at eik
    subst x'
    subst x''
    rcases same_abscissa_eq_or_neg hΔ hxy hxy' with e | e
    · exact Or.inl (hP (he.trans (e.symm.trans he'.symm)))
    rcases same_abscissa_eq_or_neg hΔ hxy hxy'' with g | g
    · exact Or.inr (Or.inl (hP (he.trans (g.symm.trans he''.symm))))
    · exact Or.inr (Or.inr (hP ((he'.trans e).trans (he''.trans g).symm)))
  have hCard := TwoPointFiberCard.card_le_two_mul a hFib
  have hT : Nat.card T ≤ f.natDegree := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact (Multiset.toFinset_card_le).trans (card_roots' f)
  exact hCard.trans (Nat.mul_le_mul_left _ hT)

end

end ManuscriptAudit.CubicAffineFiberBound

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicAffineFiberBound.card_le_of_root_abscissas
  let allowed : List Name := [``propext, `Classical.choice, `Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
