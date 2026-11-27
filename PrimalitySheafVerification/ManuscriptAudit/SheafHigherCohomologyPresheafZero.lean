import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SheafHigherCohomologyLocalVanishing

/-! Sheafification of the positive cohomology presheaf vanishes. -/

namespace ManuscriptAudit.SheafHigherCohomologyPresheafZero

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits ConcreteCategory Opposite
open SheafHigherCohomologyLocalVanishing

universe u v w

noncomputable section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

private abbrev A := AddCommGrpCat.{v}
private abbrev S := Sheaf J A

variable [HasSheafify J A] [HasExt.{w} (S J)] [EnoughInjectives (S J)]
variable [J.HasSheafCompose (forget A)] [J.WEqualsLocallyBijective A]
variable [HasFunctorialSurjectiveInjectiveFactorization A]

theorem sheafified_isZero (n : ℕ) (F : S J) :
    IsZero ((presheafToSheaf J A).obj (F.cohomologyPresheaf (n+1))) := by
  let Z : Cᵒᵖ ⥤ A := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (PUnit : Type v))
  let P := presheafToSheaf J A
  let η : F.cohomologyPresheaf (n+1) ⟶ Z := 0
  have hZ : IsZero Z := Functor.isZero _ (fun _ => AddCommGrpCat.isZero_of_subsingleton _)
  have hInj : Presheaf.IsLocallyInjective J η := by
    constructor
    intro U x y _
    have hs := vanishingSieve_covering J n F U.unop (x-y)
    refine J.superset_covering ?_ hs
    intro V g hg
    change (F.cohomologyPresheaf (n+1)).map g.op (x-y) = 0 at hg
    change (F.cohomologyPresheaf (n+1)).map g.op x =
      (F.cohomologyPresheaf (n+1)).map g.op y
    rw [map_sub] at hg
    exact sub_eq_zero.mp hg
  have hSurj : Presheaf.IsLocallySurjective J η := by
    constructor
    intro U x
    refine J.superset_covering ?_ (J.top_mem U)
    intro V g _
    refine ⟨0, ?_⟩
    exact Subsingleton.elim (α := (PUnit : Type v)) _ _
  letI : IsIso (P.map η) := (J.W_iff η).mp
    ((J.W_iff_isLocallyBijective η).mpr ⟨hInj, hSurj⟩)
  exact (P.map_isZero hZ).of_iso (asIso (P.map η))

end
end ManuscriptAudit.SheafHigherCohomologyPresheafZero

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SheafHigherCohomologyPresheafZero.sheafified_isZero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
