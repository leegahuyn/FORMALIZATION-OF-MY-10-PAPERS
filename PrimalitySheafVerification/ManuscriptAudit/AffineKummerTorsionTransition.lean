import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineKummer

/-! Multiplication on genuine Kummer kernels and their actual affine H¹. -/

namespace ManuscriptAudit.AffineKummerTorsionTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open KummerSheafSequence KummerCohomologySequence KummerCohomologyDegreeTwo
open WeierstrassAffineKummer

noncomputable section

attribute [local instance] affineSiteHasExt

private theorem sheafPower_comp (R : CommRingCat.{0}) (d m : ℕ) :
    sheafPower (Spec R) m ≫ sheafPower (Spec R) d = sheafPower (Spec R) (d * m) := by
  simp only [sheafPower_eq_nsmul_id, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp, smul_smul]

/-- The actual power map from the Kummer kernel of dm to the kernel of d. -/
def rootsTransition (R : CommRingCat.{0}) (d m : ℕ) :
    powerKernel R (d * m) ⟶ powerKernel R d :=
  kernel.lift (sheafPower (Spec R) d)
    (kernel.ι (sheafPower (Spec R) (d * m)) ≫ sheafPower (Spec R) m) (by
      rw [Category.assoc, sheafPower_comp, kernel.condition])

theorem rootsTransition_ι (R : CommRingCat.{0}) (d m : ℕ) :
    rootsTransition R d m ≫ kernel.ι (sheafPower (Spec R) d) =
      kernel.ι (sheafPower (Spec R) (d * m)) ≫ sheafPower (Spec R) m := by
  simp [rootsTransition]

/-- The matching transition between genuine killed-by subgroups. -/
def killedByTransition (G : Type) [AddCommGroup G] (d m : ℕ) :
    killedBy G (d * m) →+ killedBy G d where
  toFun x := ⟨m • x.val, by
    change d • (m • x.val) = 0
    rw [smul_smul]
    exact x.property⟩
  map_zero' := Subtype.ext (nsmul_zero m)
  map_add' x y := Subtype.ext (nsmul_add _ _ _)

/-- At degree one the actual Kummer transition is multiplication on unit
cohomology torsion, with the literal coefficient-kernel inclusions. -/
theorem degreeOneKernelEquiv_transition (R : CommRingCat.{0}) (d m : ℕ)
    (hdpos : 0 < d) (hprodpos : 0 < d * m)
    (hd : IsUnit (d : R)) (hprod : IsUnit ((d * m : ℕ) : R))
    (hu : Function.Surjective (fun u : Rˣ => u ^ d))
    (hup : Function.Surjective (fun u : Rˣ => u ^ (d * m)))
    (x : Sheaf.H (powerKernel R (d * m)) 1) :
    degreeOneKernelEquiv R d hdpos hd hu (Sheaf.H.map (rootsTransition R d m) 1 x) =
      killedByTransition (Sheaf.H (unitSheaf (Spec R)) 1) d m
        (degreeOneKernelEquiv R (d * m) hprodpos hprod hup x) := by
  apply Subtype.ext
  let i := kernel.ι (sheafPower (Spec R) d)
  let j := kernel.ι (sheafPower (Spec R) (d * m))
  let g := sheafPower (Spec R) m
  let f := rootsTransition R d m
  change Sheaf.H.map i 1 (Sheaf.H.map f 1 x) = m • Sheaf.H.map j 1 x
  calc
    _ = Sheaf.H.map (f ≫ i) 1 x := (Sheaf.H.map_comp_apply f i x).symm
    _ = Sheaf.H.map (j ≫ g) 1 x := congrArg (fun a => Sheaf.H.map a 1 x) (rootsTransition_ι R d m)
    _ = Sheaf.H.map g 1 (Sheaf.H.map j 1 x) := Sheaf.H.map_comp_apply j g x
    _ = _ := cohomologyPower_apply R m 1 (Sheaf.H.map j 1 x)

end

end ManuscriptAudit.AffineKummerTorsionTransition

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineKummerTorsionTransition.rootsTransition_ι,
      ``ManuscriptAudit.AffineKummerTorsionTransition.degreeOneKernelEquiv_transition] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
