import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleKummerLabelComparison
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicFrobeniusLabel
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicHOneLimit

/-! The genuine compatible cyclic tower maps to the actual unit Tate
module with exactly the same constituent full-site unit labels. -/

namespace ManuscriptAudit.FullEtaleCyclicUnitTate

open AlgebraicGeometry CategoryTheory
open KummerUnitsSheaf EtaleKummerCyclicCoordinates PowerTateModule
open FullEtaleKummerConstantTransition FullEtaleKummerLabelComparison
open FullEtaleCyclicFrobeniusLabel FullEtaleConstantRootLabel

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) (l : ℕ) [Fact l.Prime]
variable {K : Type} [Field K] [IsAlgClosed K] [NeZero (l : K)]
variable (k : X ⟶ Spec (CommRingCat.of K))
variable (hu : ∀ n : ℕ, Function.Surjective (fun u : (Γ(X, ⊤))ˣ => u ^ (l ^ n)))

private abbrev C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}
private abbrev U := fullCoordinateUnitSheaf X
private abbrev S := KummerRelativeFull.sequence X
private abbrev u (d : ℕ) := KummerRelativeFull.unitsIso (X := X) d

/-- Untwisted actual compatible cyclic H¹ identifies additively with
the actual Tate module of unit cohomology by the coherent roots. -/
def cyclicUnitTateEquiv :
    ↥(FullEtaleCyclicHOneLimit.compatible X l) ≃+ Tate l (Sheaf.H (U X) 1) :=
  (FullEtaleCyclicHOneLimit.rootsEquiv X l k).trans (FullEtaleKummerTateLimit.tateEquiv X l k hu)

private theorem cyclicLabel_sequence (n : ℕ) :
    ((C X).map (cyclicIso K l n).hom ≫ (constantKernelIso k l n).hom) ≫
      (S X (l ^ n)).f ≫ (u X 1).inv = cyclicUnitLabel K l k n := by
  let e := u X (l ^ n)
  let f := (S X (l ^ n)).f
  let c := (constantKernelIso k l n).hom
  let t := (C X).map (cyclicIso K l n).hom
  have hx : c ≫ f ≫ e.inv = unitLabel k (l ^ n) := by
    calc
      _ = (c ≫ f) ≫ e.inv := (Category.assoc _ _ _).symm
      _ = (unitLabel k (l ^ n) ≫ e.hom) ≫ e.inv :=
        congrArg (· ≫ e.inv) (unitLabel_eq_kummer k l n).symm
      _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (t ≫ c) ≫ f ≫ e.inv = t ≫ unitLabel k (l ^ n)
  rw [Category.assoc, hx]

/-- Evaluation of the actual Tate comparison at each level equals the
map in degree one of the literal full-site cyclic Kummer label. -/
theorem cyclicUnitTateEquiv_value (x : FullEtaleCyclicHOneLimit.compatible X l) (n : ℕ) :
    ((evaluate l (Sheaf.H (U X) 1) n (cyclicUnitTateEquiv X l k hu x)) : Sheaf.H (U X) 1) =
      Sheaf.H.map (cyclicUnitLabel K l k n) 1 (x.val n) := by
  let c := (constantKernelIso k l n).hom
  let t := (C X).map (cyclicIso K l n).hom
  let f := (S X (l ^ n)).f
  change Sheaf.H.map (u X 1).inv 1
    (Sheaf.H.map f 1 (Sheaf.H.map (t ≫ c) 1 (x.val n))) = _
  rw [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun g => Sheaf.H.map g 1 (x.val n)) (cyclicLabel_sequence X l k n)

end

end ManuscriptAudit.FullEtaleCyclicUnitTate

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FullEtaleCyclicUnitTate.cyclicUnitTateEquiv_value
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
