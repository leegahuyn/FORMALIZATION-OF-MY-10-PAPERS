import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.FullEtaleCyclicHOneLimit
import PrimalitySheafVerification.ManuscriptAudit.PadicBoundedTorsionTower

/-! The genuine cyclic and Kummer finite cohomology groups have the
native actions of their corresponding finite quotient rings. -/

namespace ManuscriptAudit.FullEtaleHOnePadic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open EtaleKummerCyclicCoordinates FullEtaleKummerKernel

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0})

private abbrev A := AddCommGrpCat.{0}
private abbrev C := Sheaf X.smallEtaleTopology A

private theorem cohomology_killed {F : C X} (d : ℕ) (h : d • 𝟙 F = 0)
    (x : Sheaf.H F 1) : d • x = 0 := by
  let E := Sheaf.functorH X.smallEtaleTopology 1
  calc
    _ = (E.map (d • 𝟙 F)).hom x := by rw [Functor.map_nsmul, E.map_id] <;> rfl
    _ = 0 := by rw [h, Functor.map_zero] <;> rfl

private abbrev S := KummerRelativeFull.sequence X

private theorem roots_killed (d : ℕ) : d • 𝟙 (S X d).X₁ = 0 := by
  let E := (Scheme.AffineEtale.sheafEquiv X A).functor
  let p := KummerSheafSequence.sheafPower X d
  letI : Mono ((S X d).f) := inferInstanceAs (Mono (E.map (kernel.ι p)))
  apply (cancel_mono (S X d).f).mp
  calc
    _ = (S X d).f ≫ (d • 𝟙 (S X d).X₂) := by
      rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
    _ = 0 := by rw [← KummerRelativeFull.power_nsmul, (S X d).zero]
    _ = _ := (zero_comp _ _).symm

private theorem cyclic_killed (d : ℕ) :
    d • 𝟙 ((constantSheaf X.smallEtaleTopology A).obj (AddCommGrpCat.of (ZMod d))) = 0 := by
  let E := constantSheaf X.smallEtaleTopology A
  let M := AddCommGrpCat.of (ZMod d)
  letI : E.Additive := Functor.additive_of_preserves_binary_products E
  have h : d • 𝟙 M = 0 := by
    apply AddCommGrpCat.ext
    intro x
    change d • x = 0
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod d), ZMod.natCast_self, zero_smul]
  calc
    _ = E.map (d • 𝟙 M) := by rw [Functor.map_nsmul, E.map_id]
    _ = 0 := by rw [h, Functor.map_zero]

variable (l : ℕ)

instance rootsModule (n : ℕ) :
    Module (ZMod (l ^ n)) (FullEtaleKummerTateLimit.Level X l n) :=
  AddCommGroup.zmodModule (cohomology_killed X (l ^ n) (roots_killed X (l ^ n)))

instance cyclicModule (n : ℕ) :
    Module (ZMod (l ^ n)) (FullEtaleCyclicHOneLimit.Level X l n) :=
  AddCommGroup.zmodModule (cohomology_killed X (l ^ n) (cyclic_killed X (l ^ n)))

variable [Fact l.Prime]

/-- Native twisted H¹ as a module over the prime-adic integers. -/
abbrev RootsHOne :=
  ↥(PadicBoundedTorsionTower.compatible l (FullEtaleKummerTateLimit.Level X l)
    (FullEtaleKummerTateLimit.step X l))

/-- Native untwisted H¹ as a module over the prime-adic integers. -/
abbrev CyclicHOne :=
  ↥(PadicBoundedTorsionTower.compatible l (FullEtaleCyclicHOneLimit.Level X l)
    (FullEtaleCyclicHOneLimit.step X l))

end

end ManuscriptAudit.FullEtaleHOnePadic

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.FullEtaleHOnePadic.rootsModule,
      ``ManuscriptAudit.FullEtaleHOnePadic.cyclicModule] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
