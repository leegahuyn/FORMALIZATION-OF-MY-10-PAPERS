import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import PrimalitySheafVerification.ManuscriptAudit.MappedCechNerve
import PrimalitySheafVerification.ManuscriptAudit.SetCechAcyclic

/-! Geometric skyscrapers have zero positive Čech cohomology
for an actual singleton covering arrow. -/

namespace ManuscriptAudit.SkyscraperCechAcyclic

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] [LocallySmall.{w} C]
variable {J : GrothendieckTopology C} {U T : C} (f : U ⟶ T)

private abbrev A := AddCommGrpCat.{w}

/-- The native Čech cochain complex of an abelian sheaf over one arrow. -/
def cochains (F : Sheaf J A.{w}) : CochainComplex A.{w} ℕ :=
  (alternatingCofaceMapComplex A.{w}).obj ((Arrow.mk f).cechNerve.rightOp ⋙ F.obj)

variable (Φ : J.Point.{w}) (M : A.{w})

/-- The actual Čech cochains of a skyscraper identify with cochains
on the point's fiber sets. -/
def cochainsIsoSetCochains :
    cochains f (Φ.skyscraperSheaf M) ≅
      SetCechAcyclic.cochains (Φ.fiber.map f) ((piFunctor.{w} (C := A.{w})).obj M) := by
  let N := (Arrow.mk f).cechNerve
  let L := (Arrow.mk (Φ.fiber.map f)).cechNerve
  let P := (piFunctor.{w} (C := A.{w})).obj M
  let e : N ⋙ Φ.fiber ≅ L := MappedCechNerve.mapCechNerveIso Φ.fiber f
  let eo : N.rightOp ⋙ Φ.fiber.op ≅ L.rightOp :=
    NatIso.ofComponents (fun n ↦ (e.app (op n)).symm.op) (fun {m n} g ↦ by
      apply Quiver.Hom.unop_inj
      change e.inv.app (op n) ≫ (N ⋙ Φ.fiber).map g.op =
        L.map g.op ≫ e.inv.app (op m)
      exact (e.inv.naturality g.op).symm)
  let ep : N.rightOp ⋙ (Φ.fiber.op ⋙ P) ≅ L.rightOp ⋙ P :=
    (CategoryTheory.Functor.associator _ _ _).symm ≪≫
      CategoryTheory.Functor.isoWhiskerRight eo P
  exact (alternatingCofaceMapComplex A.{w}).mapIso ep

/-- The genuine cochain complex of the skyscraper has no positive
homology on a covering arrow, in every degree. -/
theorem H_succ_isZero (hf : Sieve.generate (Presieve.singleton f) ∈ J T) (n : ℕ) :
    IsZero ((cochains f (Φ.skyscraperSheaf M)).homology (n + 1)) := by
  let P := (piFunctor.{w} (C := A.{w})).obj M
  have hSurj := MappedCechNerve.pointFiber_cover_surjective Φ f hf
  have h := SetCechAcyclic.H_succ_isZero (Φ.fiber.map f) P hSurj n
  exact h.of_iso ((HomologicalComplex.homologyFunctor A.{w} (.up ℕ) (n + 1)).mapIso
    (cochainsIsoSetCochains f Φ M))

end

end ManuscriptAudit.SkyscraperCechAcyclic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.SkyscraperCechAcyclic.H_succ_isZero
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
