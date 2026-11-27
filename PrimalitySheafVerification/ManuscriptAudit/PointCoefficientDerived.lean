import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FiniteClosedSkyscraperHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientSheaf

/-! The native derived cohomology of the point-coefficient sheaf on finite closed support. -/

namespace ManuscriptAudit.PointCoefficientDerived

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open PointCoefficientSheaf ClosedSupportDetection FiniteClosedSkyscraperHigherCohomology

noncomputable section

variable {X : TopCat.{0}} (P : Set X) (A : P → Type)
variable [∀ p : P, AddCommGroup (A p)]

local instance (Y : TopCat.{0}) : HasExt.{0} (AbelianSheaf Y) := IsGrothendieckAbelian.hasExt _

private abbrev pointSheaf : AbelianSheaf X := sheaf P A

private def topSectionsEquiv : Sections P A (⊤ : Opens X) ≃+ (∀ p : P, A p) where
  toFun s p := s ⟨p, Opens.mem_top _⟩
  invFun f q := f q.val
  left_inv s := by funext q; cases q; rfl
  right_inv f := rfl
  map_add' _ _ := rfl

/-- Actual degree-zero Zariski cohomology is the full product of the coefficients. -/
def HZeroEquiv : (pointSheaf P A).H 0 ≃+ (∀ p : P, A p) := by
  let hT : IsTerminal (⊤ : Opens X) :=
    IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)
  exact (Sheaf.H.equiv₀ (pointSheaf P A) hT).trans (topSectionsEquiv P A)

theorem stalk_subsingleton_outside (hP : IsClosed P) {x : X} (hx : x ∉ P) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (presheaf P A) x) := by
  let F := presheaf P A
  let V : Opens X := ⟨Pᶜ, hP.isOpen_compl⟩
  have hxV : x ∈ V := hx
  apply subsingleton_of_forall_eq 0
  intro t
  obtain ⟨U, hUV, hxU, s, hs⟩ := F.exists_le_germ_eq (x := x) t hxV
  have hs0 : s = 0 := by
    change s = (0 : Sections P A U)
    funext q
    have hpV : q.val.val ∈ V := hUV q.property
    exact (hpV q.val.property).elim
  rw [← hs, hs0, map_zero]

theorem stalkSupport_subset (hP : IsClosed P) : stalkSupport (sheaf P A) ⊆ P := by
  intro x hx
  by_contra hn
  letI := stalk_subsingleton_outside P A hP hn
  change Nontrivial (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (presheaf P A) x) at hx
  exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hx

/-- Every positive-degree native Zariski group is zero for finite closed point support. -/
theorem H_succ_subsingleton [Finite P]
    (hP : IsClosed P) (hPoint : ∀ p ∈ P, IsClosed ({p} : Set X)) (n : ℕ) :
    Subsingleton ((pointSheaf P A).H (n + 1)) :=
  H_succ_subsingleton_of_finite_closed_support (sheaf P A) P
    hPoint (stalkSupport_subset P A hP) n

end
end ManuscriptAudit.PointCoefficientDerived

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientDerived.HZeroEquiv,
      ``ManuscriptAudit.PointCoefficientDerived.stalk_subsingleton_outside,
      ``ManuscriptAudit.PointCoefficientDerived.H_succ_subsingleton] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
